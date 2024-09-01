module CSlash.Platform.Ways where

import CSlash.Platform
import CSlash.Driver.Flags

import qualified Data.Set as Set
import Data.Set (Set)
import Data.List (intersperse)

data Way
  = WayCustom String
  | WayThreaded
  | WayDebug
  | WayProf
  | WayDyn
  deriving (Eq, Ord, Show)

type Ways = Set Way
