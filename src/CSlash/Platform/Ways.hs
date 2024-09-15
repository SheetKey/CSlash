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

addWay :: Way -> Ways -> Ways
addWay = Set.insert

waysTag :: Ways -> String
waysTag = concat . intersperse "_" . map wayTag . Set.toAscList

waysBuildTag :: Ways -> String
waysBuildTag ws = waysTag (Set.filter (not . wayRTSOnly) ws)

wayTag :: Way -> String
wayTag (WayCustom xs) = xs
wayTag WayThreaded = "thr"
wayTag WayDebug = "debug"
wayTag WayDyn = "dyn"
wayTag WayProf = "p"

wayRTSOnly :: Way -> Bool
wayRTSOnly (WayCustom{}) = False
wayRTSOnly WayDyn = False
wayRTSOnly WayProf = False
wayRTSOnly WayThreaded = True
wayRTSOnly WayDebug = True
