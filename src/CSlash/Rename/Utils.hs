module CSlash.Rename.Utils where

import Prelude hiding (unzip)

import CSlash.Core.Type
import CSlash.Cs
import CSlash.Types.Name.Reader
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad
import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.Name.Env
import CSlash.Core.DataCon
import CSlash.Types.SrcLoc as SrcLoc
import CSlash.Types.SourceFile
import CSlash.Types.SourceText ( SourceText(..), IntegralLit )
import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Unit.Module.ModIface
import CSlash.Utils.Panic
import CSlash.Types.Basic
import CSlash.Data.List.SetOps ( removeDupsOn )
import CSlash.Data.Maybe ( whenIsJust )
import CSlash.Driver.DynFlags
import CSlash.Data.FastString
import CSlash.Data.Bag ( mapBagM, headMaybe )
import Control.Monad
import CSlash.Settings.Constants ( mAX_TUPLE_SIZE{-, mAX_CTUPLE_SIZE-} )
import CSlash.Unit.Module
import CSlash.Unit.Module.Warnings  ( WarningTxt(..) )
import CSlash.Iface.Load

import qualified Data.List as List
import qualified Data.List.NonEmpty as NE
import Data.Foldable
import Data.Maybe

{- *****************************************************
*                                                      *
            Binding
*                                                      *
***************************************************** -}

newLocalBndrRn :: LocatedN RdrName -> RnM Name
newLocalBndrRn (L loc rdr_name)
  | Just name <- isExact_maybe rdr_name
  = return name
  | otherwise
  = do unless (isUnqual rdr_name) $ addErrAt (locA loc) (badQualBndrErr rdr_name)
       uniq <- newUnique
       return $ mkInternalName uniq (rdrNameOcc rdr_name) (locA loc)

bindLocalNames :: [Name] -> RnM a -> RnM a
bindLocalNames names = updLclCtxt $ \lcl_env ->
  let rdr_env' = extendLocalRdrEnvList (tcl_rdr lcl_env) names
  in lcl_env { tcl_rdr = rdr_env' }

bindLocalNamesFV :: [Name] -> RnM (a, FreeVars) -> RnM (a, FreeVars)
bindLocalNamesFV names enclosed_scope = do
  (result, fvs) <- bindLocalNames names enclosed_scope
  return (result, delFVs names fvs)

checkDupRdrNames :: [LocatedN RdrName] -> RnM ()
checkDupRdrNames rdr_names_w_loc
  = mapM_ (\ns -> dupNamesErr (getLocA <$> ns) (unLoc <$> ns)) dups
  where
    (_, dups) = removeDupsOn unLoc rdr_names_w_loc

checkDupNames :: [Name] -> RnM ()
checkDupNames names = check_dup_names (filterOut isSystemName names)

check_dup_names :: [Name] -> RnM ()
check_dup_names names = mapM_ (\ns -> dupNamesErr (nameSrcSpan <$> ns) (getRdrName <$> ns)) dups
  where
    (_, dups) = removeDupsOn nameOccName names

checkShadowedRdrNames :: [LocatedN RdrName] -> RnM ()
checkShadowedRdrNames loc_rdr_names = do
  envs <- getRdrEnvs
  checkShadowedOccs envs get_loc_occ filtered_rdrs
  where
    filtered_rdrs = filterOut (isExact . unLoc) loc_rdr_names
    get_loc_occ (L loc rdr) = (locA loc, rdrNameOcc rdr)

checkDupAndShadowedNames :: (GlobalRdrEnv, LocalRdrEnv) -> [Name] -> RnM ()
checkDupAndShadowedNames envs names = do
  check_dup_names filtered_names
  checkShadowedOccs envs get_loc_occ filtered_names
  where
    filtered_names = filterOut isSystemName names
    get_loc_occ name = (nameSrcSpan name, nameOccName name)

checkShadowedOccs :: (GlobalRdrEnv, LocalRdrEnv) -> (a -> (SrcSpan, OccName)) -> [a] -> RnM ()
checkShadowedOccs (global_env, local_env) get_loc_occ ns
  = whenWOptM Opt_WarnNameShadowing $ do
    traceRn "checkShadowedOccs:shadow" (ppr (map get_loc_occ ns))
    mapM_ check_shadow ns
  where
    check_shadow n
      | startsWithUnderscore occ = return ()
      | Just n <- mb_local = complain (ShadowedNameProvenanceLocal (nameSrcLoc n))
      | otherwise = when (not . null $ gres) $
                    complain (ShadowedNameProvenanceGlobal gres)
      where
        (loc, occ) = get_loc_occ n
        mb_local = lookupLocalRdrOcc local_env occ
        gres = lookupGRE global_env (LookupRdrName (mkRdrUnqual occ) (RelevantGREs False))

        complain provenance = addDiagnosticAt loc (TcRnShadowedName occ provenance)

{- *********************************************************************
*                                                                      *
            Free variable manipulation
*                                                                      *
********************************************************************* -}

mapFvRn :: Traversable f => (a -> RnM (b, FreeVars)) -> f a -> RnM (f b, FreeVars)
mapFvRn f xs = do
  stuff <- mapM f xs
  case unzip stuff of
    (ys, fvs_s) -> return (ys, foldl' (flip plusFV) emptyFVs fvs_s)
{-# SPECIALIZE mapFvRn :: (a -> RnM (b, FreeVars)) -> [a] -> RnM ([b], FreeVars) #-}

unzip :: Functor f => f (a, b) -> (f a, f b)
unzip = \xs -> (fmap fst xs, fmap snd xs)
{-# NOINLINE [1] unzip #-}
{-# RULES "unzip/List" unzip = List.unzip #-}

{- *********************************************************************
*                                                                      *
            Envt utility functions
*                                                                      *
********************************************************************* -}

warnUnusedTopBinds :: [GlobalRdrElt] -> ZkM ()
warnUnusedTopBinds gres = whenWOptM Opt_WarnUnusedTopBinds $ warnUnusedGREs gres

warnUnusedLocalBinds :: [Name] -> FreeVars -> RnM ()
warnUnusedLocalBinds = check_unused UnusedNameLocalBind

warnUnusedMatches :: [Name] -> FreeVars -> RnM ()
warnUnusedMatches = check_unused UnusedNameMatch

check_unused :: UnusedNameProv -> [Name] -> FreeVars -> RnM ()
check_unused prov bound_names used_names
  = warnUnused prov (filterOut (`elemNameSet` used_names) bound_names)

warnUnusedGREs :: [GlobalRdrElt] -> ZkM ()
warnUnusedGREs gres = mapM_ warnUnusedGRE gres

warnUnused :: UnusedNameProv -> [Name] -> RnM ()
warnUnused prov names = mapM_ (\nm -> warnUnused1 prov nm (nameOccName nm)) names

warnUnused1 :: UnusedNameProv -> Name -> OccName -> TcRnZk p ()
warnUnused1 prov child child_occ
  = when (reportable child child_occ) $
    warn_unused_name prov (nameSrcSpan child) child_occ

warn_unused_name :: UnusedNameProv -> SrcSpan -> OccName -> TcRnZk p ()
warn_unused_name prov span child_occ = addDiagnosticAt span (TcRnUnusedName child_occ prov)

warnUnusedGRE :: GlobalRdrElt -> ZkM ()
warnUnusedGRE gre@(GRE { gre_lcl = lcl, gre_imp = is })
  | lcl = warnUnused1 UnusedNameTopDecl nm occ
  | otherwise = when (reportable nm occ) (mapM_ warn is)
  where
    occ = greOccName gre
    nm = greName gre
    warn spec = warn_unused_name (UnusedNameImported (importSpecModule spec)) span occ
      where span = importSpecLoc spec

reportable :: Name -> OccName -> Bool
reportable child child_occ
  | isWiredInName child
  = False
  | otherwise
  = not (startsWithUnderscore child_occ)

addNameClashErrRn :: RdrName -> NE.NonEmpty GlobalRdrElt -> RnM ()
addNameClashErrRn rdr_name gres
  | all isLocalGRE gres && length gres >= 2
  = return ()
  | otherwise
  = do gre_env <- getGlobalRdrEnv
       addErr $ mkNameClashErr gre_env rdr_name gres

mkNameClashErr :: GlobalRdrEnv -> RdrName -> NE.NonEmpty GlobalRdrElt -> TcRnMessage
mkNameClashErr gre_Env rdr_name gres = panic "TcRnAmbiguousName gre_env rdr_name gres"

dupNamesErr :: NE.NonEmpty SrcSpan -> NE.NonEmpty RdrName -> RnM ()
dupNamesErr locs names
  = addErrAt big_loc (TcRnBindingNameConflict (NE.head names) locs)
  where big_loc =foldr1 combineSrcSpans locs

badQualBndrErr :: RdrName -> TcRnMessage
badQualBndrErr rdr_name = TcRnQualifiedBinder rdr_name

checkTupSize :: Int -> TcM ()
checkTupSize tup_size
  | tup_size <= mAX_TUPLE_SIZE
  = return ()
  | otherwise
  -- = addErr (TcRnTupleTooLarge tup_size)
  = panic "checkTupSize"

{- *********************************************************************
*                                                                      *
              Generating code for expanded exprs
*                                                                      *
********************************************************************* -}

wrapGenSpan :: (NoAnn an) => a -> LocatedAn an a
wrapGenSpan x = L (noAnnSrcSpan generatedSrcSpan) x

genCsApps :: Name -> [LCsExpr Rn] -> CsExpr Rn
genCsApps fun args = foldl genCsApp (genCsVar fun) args

genCsApp :: CsExpr Rn -> LCsExpr Rn -> CsExpr Rn
genCsApp fun arg = CsApp noExtField (wrapGenSpan fun) arg

genCsVar :: Name -> CsExpr Rn
genCsVar nm = CsVar noExtField $ wrapGenSpan nm

{- *********************************************************************
*                                                                      *
              Generating code for expanded types
*                                                                      *
********************************************************************* -}

genCsTyVar :: Name -> CsType Rn
genCsTyVar nm = CsTyVar noAnn $ wrapGenSpan nm

genCsTyApps :: Name -> [LCsType Rn] -> CsType Rn
genCsTyApps fun args = foldl genCsTyApp (genCsTyVar fun) args

genCsTyApp :: CsType Rn -> LCsType Rn -> CsType Rn
genCsTyApp fun arg = CsAppTy noExtField (wrapGenSpan fun) arg
