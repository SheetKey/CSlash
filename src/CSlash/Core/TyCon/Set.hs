module CSlash.Core.TyCon.Set where

import CSlash.Cs.Pass

import CSlash.Types.Unique.Set
import CSlash.Core.TyCon (TyCon)
import CSlash.Types.Var (TyVar, KiVar)

type TyConSet = UniqSet (TyCon Zk)

isEmptyTyConSet :: TyConSet -> Bool
isEmptyTyConSet    = isEmptyUniqSet

emptyTyConSet :: TyConSet
emptyTyConSet = emptyUniqSet

unitTyConSet :: TyCon Zk -> TyConSet
unitTyConSet = unitUniqSet

mkTyConSet :: [TyCon Zk] -> TyConSet
mkTyConSet = mkUniqSet

extendTyConSet :: TyConSet -> TyCon Zk -> TyConSet
extendTyConSet = addOneToUniqSet

extendTyConSetList :: TyConSet -> [TyCon Zk] -> TyConSet
extendTyConSetList = addListToUniqSet

unionTyConSet :: TyConSet -> TyConSet -> TyConSet
unionTyConSet = unionUniqSets

unionTyConSets :: [TyConSet] -> TyConSet
unionTyConSets = unionManyUniqSets

minusTyConSet :: TyConSet -> TyConSet -> TyConSet
minusTyConSet = minusUniqSet

elemTyConSet :: TyCon Zk -> TyConSet -> Bool
elemTyConSet = elementOfUniqSet

filterTyConSet :: (TyCon Zk -> Bool) -> TyConSet -> TyConSet
filterTyConSet = filterUniqSet

disjointTyConSet :: TyConSet -> TyConSet -> Bool
disjointTyConSet = disjointUniqSets

delFromTyConSet :: TyConSet -> TyCon Zk -> TyConSet
delFromTyConSet = delOneFromUniqSet

delListFromTyConSet :: TyConSet -> [TyCon Zk] -> TyConSet
delListFromTyConSet set ns = foldl' delFromTyConSet set ns

intersectTyConSet :: TyConSet -> TyConSet -> TyConSet
intersectTyConSet = intersectUniqSets

intersectsTyConSet :: TyConSet -> TyConSet -> Bool
intersectsTyConSet s1 s2 = not (isEmptyTyConSet (s1 `intersectTyConSet` s2))

nameSetAny :: (TyCon Zk -> Bool) -> TyConSet -> Bool
nameSetAny = uniqSetAny

nameSetAll :: (TyCon Zk -> Bool) -> TyConSet -> Bool
nameSetAll = uniqSetAll
