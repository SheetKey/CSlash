module CSlash.Core.TyCon.Set where

import CSlash.Types.Unique.Set
import CSlash.Core.TyCon (TyCon)

type TyConSet = UniqSet TyCon

isEmptyTyConSet :: TyConSet -> Bool
isEmptyTyConSet    = isEmptyUniqSet

emptyTyConSet :: TyConSet
emptyTyConSet = emptyUniqSet

unitTyConSet :: TyCon -> TyConSet
unitTyConSet = unitUniqSet

mkTyConSet :: [TyCon] -> TyConSet
mkTyConSet = mkUniqSet

extendTyConSet :: TyConSet -> TyCon -> TyConSet
extendTyConSet = addOneToUniqSet

extendTyConSetList :: TyConSet -> [TyCon] -> TyConSet
extendTyConSetList = addListToUniqSet

unionTyConSet :: TyConSet -> TyConSet -> TyConSet
unionTyConSet = unionUniqSets

unionTyConSets :: [TyConSet] -> TyConSet
unionTyConSets = unionManyUniqSets

minusTyConSet :: TyConSet -> TyConSet -> TyConSet
minusTyConSet = minusUniqSet

elemTyConSet :: TyCon -> TyConSet -> Bool
elemTyConSet = elementOfUniqSet

filterTyConSet :: (TyCon -> Bool) -> TyConSet -> TyConSet
filterTyConSet = filterUniqSet

disjointTyConSet :: TyConSet -> TyConSet -> Bool
disjointTyConSet = disjointUniqSets

delFromTyConSet :: TyConSet -> TyCon -> TyConSet
delFromTyConSet = delOneFromUniqSet

delListFromTyConSet :: TyConSet -> [TyCon] -> TyConSet
delListFromTyConSet set ns = foldl' delFromTyConSet set ns

intersectTyConSet :: TyConSet -> TyConSet -> TyConSet
intersectTyConSet = intersectUniqSets

intersectsTyConSet :: TyConSet -> TyConSet -> Bool
intersectsTyConSet s1 s2 = not (isEmptyTyConSet (s1 `intersectTyConSet` s2))

nameSetAny :: (TyCon -> Bool) -> TyConSet -> Bool
nameSetAny = uniqSetAny

nameSetAll :: (TyCon -> Bool) -> TyConSet -> Bool
nameSetAll = uniqSetAll
