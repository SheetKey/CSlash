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
import CSlash.Builtin.Names ( mkUnboundName, isUnboundName{-, getUnique-})
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
  = panic "similarNameSuggestions"

importSuggestions
  :: LookingFor
  -> GlobalRdrEnv
  -> HomePackageTable
  -> Module
  -> ImportAvails
  -> RdrName
  -> ([ImportError], [ImportSuggestion])
importSuggestions looking_for global_env hpt currMod imports rdr_name = panic "importSuggestions"
