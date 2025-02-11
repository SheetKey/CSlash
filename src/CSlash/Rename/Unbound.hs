{-# LANGUAGE PatternSynonyms #-}

module CSlash.Rename.Unbound
  ( module CSlash.Rename.Unbound
  , isUnboundName
  ) where

import Prelude hiding ((<>))

import CSlash.Driver.DynFlags
import CSlash.Driver.Ppr

import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad
import CSlash.Builtin.Names ( mkUnboundName, isUnboundName, getUnique)
import CSlash.Utils.Misc
import CSlash.Utils.Panic (panic)

import CSlash.Data.Maybe
import CSlash.Data.FastString

import CSlash.Types.Hint
  ( CsHint (ImportSuggestion, SuggestSimilarNames)
  , ImportSuggestion(..), SimilarName(..), HowInScope(..) )
import CSlash.Types.SrcLoc as SrcLoc
import CSlash.Types.Name
import CSlash.Types.Name.Reader
import CSlash.Types.GREInfo
import CSlash.Types.Unique.DFM (udfmToList)

import CSlash.Unit.Module
import CSlash.Unit.Module.Imported
import CSlash.Unit.Home.ModInfo

import CSlash.Data.Bag
import CSlash.Utils.Outputable (empty)

import Data.List (sortBy, partition, nub)
import Data.List.NonEmpty ( pattern (:|), NonEmpty )
import Data.Function ( on )
import qualified Data.Semigroup as S

data WhatLooking
  = WL_Anything
  | WL_Constructor
  | WL_None
  deriving Eq

data WhereLooking
  = WL_Anywhere
  | WL_Global
  | WL_LocalTop
  | WL_LocalOnly

data LookingFor = LF
  { lf_which :: WhatLooking
  , lf_where :: WhereLooking
  }

data IsTermInTypes = NoTermInTypes

mkUnboundNameRdr :: RdrName -> Name
mkUnboundNameRdr rdr = mkUnboundName (rdrNameOcc rdr)

mkUnboudnGRE :: OccName -> GlobalRdrElt
mkUnboudnGRE occ = mkLocalGRE UnboundGRE NoParent $ mkUnboundName occ

mkUnboundGRERdr :: RdrName -> GlobalRdrElt
mkUnboundGRERdr rdr = mkLocalGRE UnboundGRE NoParent $ mkUnboundNameRdr rdr

reportUnboundName' :: WhatLooking -> RdrName -> RnM Name
reportUnboundName' what_look rdr = unboundName (LF what_look WL_Anywhere) rdr

reportUnboundName :: RdrName -> RnM Name
reportUnboundName = reportUnboundName' WL_Anything

unboundName :: LookingFor -> RdrName -> RnM Name
unboundName lf rdr = unboundNameX lf rdr []

unboundNameX :: LookingFor -> RdrName -> [CsHint] -> RnM Name
unboundNameX looking_for rdr_name hints
  = unboundNameOrTermInType NoTermInTypes looking_for rdr_name hints

unboundNameOrTermInType :: IsTermInTypes -> LookingFor -> RdrName -> [CsHint] -> RnM Name
unboundNameOrTermInType if_term_in_type looking_for rdr_name hints = do
  dflags <- getDynFlags
  let show_helpful_errors = gopt Opt_HelpfulErrors dflags
  if not show_helpful_errors
    then addErr $ make_error [] hints
    else do local_env <- getLocalRdrEnv
            global_env <- getGlobalRdrEnv
            impInfo <- getImports
            currmod <- getModule
            hpt <- getHpt
            let (imp_errs, suggs) = unknownNameSuggestions_ looking_for dflags hpt currmod
                                    global_env local_env impInfo rdr_name
            addErr $ make_error imp_errs (hints ++ suggs)
  return $ mkUnboundNameRdr rdr_name
  where
    name_to_search = case if_term_in_type of
      NoTermInTypes -> rdr_name
    err = notInScopeErr (lf_where looking_for) name_to_search

    make_error imp_errs hints = case if_term_in_type of
      NoTermInTypes -> TcRnNotInScope err name_to_search imp_errs hints

notInScopeErr :: WhereLooking -> RdrName -> NotInScopeError
notInScopeErr where_look rdr_name
  | Just name <- isExact_maybe rdr_name
  = NoExactName name
  | WL_LocalTop <- where_look
  = NoTopLevelBinding
  | otherwise
  = NotInScope

unknownNameSuggestions_
  :: LookingFor
  -> DynFlags
  -> HomePackageTable
  -> Module
  -> GlobalRdrEnv
  -> LocalRdrEnv
  -> ImportAvails
  -> RdrName
  -> ([ImportError], [CsHint])
unknownNameSuggestions_ looking_for dflags hpt curr_mod global_env local_env imports tried_rdr_name
  = (imp_errs, suggs)
  where
    suggs = mconcat
      [ if_ne (SuggestSimilarNames tried_rdr_name) $
        similarNameSuggestions looking_for dflags global_env local_env tried_rdr_name
      , map (ImportSuggestion $ rdrNameOcc tried_rdr_name) imp_suggs
      ]
    (imp_errs, imp_suggs)
      = importSuggestions looking_for global_env hpt curr_mod imports tried_rdr_name

    if_ne :: (NonEmpty a -> b) -> [a] -> [b]
    if_ne _ [] = []
    if_ne f (a : as) = [f (a :| as)]

similarNameSuggestions
  :: LookingFor
  -> DynFlags
  -> GlobalRdrEnv
  -> LocalRdrEnv
  -> RdrName
  -> [SimilarName]
similarNameSuggestions
  looking_for@(LF what_look where_look) dflags global_env local_env tried_rdr_name
  = fuzzyLookup (showPpr dflags tried_rdr_name) all_possibilities
  where
    all_possibilities :: [(String, SimilarName)]
    all_possibilities = case what_look of
      WL_None -> []
      _ -> [ (showPpr dflags r, SimilarRdrName r (Just $ LocallyBoundAt loc))
           | (r, loc) <- local_possibilities local_env ]
        ++ [ (showPpr dflags r, rp) | (r, rp) <- global_possibilities global_env ]

    tried_occ = rdrNameOcc tried_rdr_name
    tried_is_sym = isSymOcc tried_occ
    tried_ns = occNameSpace tried_occ
    tried_is_qual = isQual tried_rdr_name

    correct_name_space occ =
      (nameSpacesRelated dflags what_look tried_ns (occNameSpace occ))
      && isSymOcc occ == tried_is_sym

    local_ok = case where_look of
                 WL_Anywhere -> True
                 WL_LocalOnly -> True
                 _ -> False

    local_possibilities :: LocalRdrEnv -> [(RdrName, SrcSpan)]
    local_possibilities env
      | tried_is_qual = []
      | not local_ok = []
      | otherwise = [ (mkRdrUnqual occ, nameSrcSpan name)
                    | name <- localRdrEnvElts env
                    , let occ = nameOccName name
                    , correct_name_space occ ]

    global_possibilities :: GlobalRdrEnv -> [(RdrName, SimilarName)]
    global_possibilities global_env
      | tried_is_qual = [ (rdr_qual, SimilarRdrName rdr_qual (Just how))
                        | gre <- globalRdrEnvElts global_env
                        , isGreOk looking_for gre
                        , let occ = greOccName gre
                        , correct_name_space occ
                        , (mod, how) <- qualsInScope gre
                        , let rdr_qual = mkRdrQual mod occ ]
      | otherwise = [ (rdr_unqual, sim)
                    | gre <- globalRdrEnvElts global_env
                    , isGreOk looking_for gre
                    , let occ = greOccName gre
                          rdr_unqual = mkRdrUnqual occ
                    , correct_name_space occ
                    , sim <- case (unquals_in_scope gre, quals_only gre) of
                               (how : _, _) -> [ SimilarRdrName rdr_unqual (Just how) ]
                               ([], pr : _) -> [ pr ]
                               ([], []) -> [] ]
                    
    unquals_in_scope :: GlobalRdrElt -> [HowInScope]
    unquals_in_scope (gre@GRE { gre_lcl = lcl, gre_imp = is })
      | lcl = [ LocallyBoundAt (greDefinitionSrcSpan gre) ]
      | otherwise = [ ImportedBy ispec
                    | i <- bagToList is
                    , let ispec = is_decl i
                    , not (is_qual ispec) ]

    quals_only :: GlobalRdrElt -> [SimilarName]
    quals_only (gre@GRE { gre_imp = is })
      = [ (SimilarRdrName (mkRdrQual (is_as ispec) (greOccName gre)) (Just $ ImportedBy ispec))
        | i <- bagToList is
        , let ispec = is_decl i
        , is_qual ispec ]

importSuggestions
  :: LookingFor
  -> GlobalRdrEnv
  -> HomePackageTable
  -> Module
  -> ImportAvails
  -> RdrName
  -> ([ImportError], [ImportSuggestion])
importSuggestions looking_for global_env hpt currMod imports rdr_name
  | WL_LocalOnly <- lf_where looking_for = ([], [])
  | WL_LocalTop <- lf_where looking_for = ([], [])
  | not (isQual rdr_name || isUnqual rdr_name) = ([], [])
  | null interesting_imports
  , Just name <- mod_name
  , show_not_imported_line name
  = ([MissingModule name], [])
  | is_qualified
  , null helpful_imports
  , (mod : mods) <- map fst interesting_imports
  = ([ModulesDoNotExport (mod :| mods) occ_name], [])
  | mod : mods <- helpful_imports_non_hiding
  = ([], [CouldImportFrom (mod :| mods)])
  | mod : mods <- helpful_imports_hiding
  = ([], [CouldUnhideFrom (mod :| mods)])
  | otherwise
  = ([], [])
  where
    is_qualified = isQual rdr_name
    (mod_name, occ_name) = case rdr_name of
      Unqual occ_name -> (Nothing, occ_name)
      Qual mod_name occ_name -> (Just mod_name, occ_name)
      _ -> panic "importSuggestions: dead code"

    interesting_imports = [ (mod, imp) | (mod, mod_imports) <- moduleEnvToList (imp_mods imports)
                                       , Just imp <- return $ pick (importedByUser mod_imports) ]

    pick = listToMaybe . sortBy cmp . filter select
      where
        select imv = case mod_name of
                       Just name -> imv_name imv == name
                       Nothing -> not (imv_qualified imv)
        cmp = on compare imv_is_hiding S.<> on SrcLoc.leftmost_smallest imv_span

    helpful_imports = filter helpful interesting_imports
      where
        helpful (_, imv) = any (isGreOk looking_for)
                           $ lookupGRE (imv_all_exports imv)
                                       (LookupOccName occ_name $ RelevantGREs False)

    (helpful_imports_hiding, helpful_imports_non_hiding)
      = partition (imv_is_hiding . snd) helpful_imports

    show_not_imported_line modname
      | modname `elem` glob_mods = False
      | moduleName currMod == modname = False
      | is_last_loaded_mod modname hpt_uniques = False
      | otherwise = True
      where
        hpt_uniques = map fst (udfmToList hpt)
        is_last_loaded_mod modname uniqs = lastMaybe uniqs == Just (getUnique modname)
        glob_mods = nub [ mod | gre <- globalRdrEnvElts global_env
                              , (mod, _) <- qualsInScope gre ]

qualsInScope :: GlobalRdrElt -> [(ModuleName, HowInScope)]
qualsInScope gre@GRE { gre_lcl = lcl, gre_imp = is }
  | lcl = case greDefinitionModule gre of
            Nothing -> []
            Just m -> [(moduleName m, LocallyBoundAt (greDefinitionSrcSpan gre))]
  | otherwise = [ (is_as ispec, ImportedBy ispec)
                | i <- bagToList is, let ispec = is_decl i ]

isGreOk :: LookingFor -> GlobalRdrElt -> Bool
isGreOk (LF what_look where_look) gre = what_ok && where_ok
  where
    what_ok = True

    where_ok = case where_look of
                 WL_LocalTop -> isLocalGRE gre
                 WL_LocalOnly -> False
                 _ -> True

nameSpacesRelated
  :: DynFlags
  -> WhatLooking
  -> NameSpace
  -> NameSpace
  -> Bool
nameSpacesRelated dflags what_looking ns ns'
  | ns == ns'
  = True
  | otherwise
  = or [ other_ns ns'
       | (orig_ns, others) <- other_namespaces
       , orig_ns ns
       , (other_ns, wls) <- others
       , what_looking `elem` WL_Anything : wls ]
  where
    other_namespaces =
      [ (isVarNameSpace, [(isDataConNameSpace, [WL_Constructor])])
      , (isTvNameSpace, [(isTcClsNameSpace, [WL_Constructor])])
      , (isTcClsNameSpace, [(isTvNameSpace, [])]) ]
