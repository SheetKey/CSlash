module CSlash.Settings.Constants where

import CSlash.Version

hiVersion :: Integer
hiVersion = read (cProjectVersionInt ++ cProjectPatchLevel) :: Integer

mAX_TUPLE_SIZE :: Int
mAX_TUPLE_SIZE = 64

mAX_SUM_SIZE :: Int
mAX_SUM_SIZE = 63

mAX_REDUCTION_DEPTH :: Int
mAX_REDUCTION_DEPTH = 200

mAX_SOLVER_ITERATIONS :: Int
mAX_SOLVER_ITERATIONS = 4
