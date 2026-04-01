module CSlash.Core.Opt.Stats where

import CSlash.Types.Var
import CSlash.Types.Error

import CSlash.Utils.Outputable as Outputable

import CSlash.Data.FastString

import Data.List (sortOn)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Ord
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Map.Strict as MapStrict
import CSlash.Utils.Panic

data SimplCount
  = VerySimplCount !Int

pprSimplCount :: SimplCount -> SDoc
pprSimplCount = panic "pprSimplCount"
