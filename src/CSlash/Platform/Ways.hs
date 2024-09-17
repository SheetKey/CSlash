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

hasWay :: Ways -> Way -> Bool
hasWay ws w = Set.member w ws

addWay :: Way -> Ways -> Ways
addWay = Set.insert

removeWay :: Way -> Ways -> Ways
removeWay = Set.delete

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

wayDesc :: Way -> String
wayDesc (WayCustom xs) = xs
wayDesc WayThreaded = "Threaded"
wayDesc WayDebug = "Debug"
wayDesc WayDyn = "Dynamic"
wayDesc WayProf = "Profiling"

wayGeneralFlags :: Platform -> Way -> [GeneralFlag]
wayGeneralFlags _ (WayCustom{}) = []
wayGeneralFlags _ WayThreaded = []
wayGeneralFlags _ WayDebug = []
wayGeneralFlags _ WayDyn = [Opt_ExternalDynamicRefs] -- no Opt_PIC since no interpreter
wayGeneralFlags _ WayProf = []

wayUnsetGeneralFlags :: Platform -> Way -> [GeneralFlag]
wayUnsetGeneralFlags _ (WayCustom{}) = []
wayUnsetGeneralFlags _ WayThreaded = []
wayUnsetGeneralFlags _ WayDebug = []
wayUnsetGeneralFlags _ WayDyn = [Opt_SplitSections]
wayUnsetGeneralFlags _ WayProf = []
