{-# LANGUAGE PatternSynonyms #-}

module CSlash.Rename.Unbound where

import Prelude hiding ((<>))

import CSlash.Driver.DynFlags
import CSlash.Driver.Ppr

import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad
-- import CSlash.Builtin.Names ( mkUnboundName, isUnboundName, getUnique)
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
