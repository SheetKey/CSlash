module CSlash.Core.TyCon.Set where

import CSlash.Types.Unique.Set
import CSlash.Core.TyCon (TyCon)
import CSlash.Types.Var (TyVar, KiVar)

type TyConSet = UniqSet (TyCon (TyVar KiVar) KiVar)

isEmptyTyConSet :: TyConSet -> Bool
isEmptyTyConSet    = isEmptyUniqSet

emptyTyConSet :: TyConSet
emptyTyConSet = emptyUniqSet

unitTyConSet :: TyCon (TyVar KiVar) KiVar -> TyConSet
unitTyConSet = unitUniqSet

mkTyConSet :: [TyCon (TyVar KiVar) KiVar] -> TyConSet
mkTyConSet = mkUniqSet

extendTyConSet :: TyConSet -> TyCon (TyVar KiVar) KiVar -> TyConSet
extendTyConSet = addOneToUniqSet

extendTyConSetList :: TyConSet -> [TyCon (TyVar KiVar) KiVar] -> TyConSet
extendTyConSetList = addListToUniqSet

unionTyConSet :: TyConSet -> TyConSet -> TyConSet
unionTyConSet = unionUniqSets

unionTyConSets :: [TyConSet] -> TyConSet
unionTyConSets = unionManyUniqSets

minusTyConSet :: TyConSet -> TyConSet -> TyConSet
minusTyConSet = minusUniqSet

elemTyConSet :: TyCon (TyVar KiVar) KiVar -> TyConSet -> Bool
elemTyConSet = elementOfUniqSet

filterTyConSet :: (TyCon (TyVar KiVar) KiVar -> Bool) -> TyConSet -> TyConSet
filterTyConSet = filterUniqSet

disjointTyConSet :: TyConSet -> TyConSet -> Bool
disjointTyConSet = disjointUniqSets

delFromTyConSet :: TyConSet -> TyCon (TyVar KiVar) KiVar -> TyConSet
delFromTyConSet = delOneFromUniqSet

delListFromTyConSet :: TyConSet -> [TyCon (TyVar KiVar) KiVar] -> TyConSet
delListFromTyConSet set ns = foldl' delFromTyConSet set ns

intersectTyConSet :: TyConSet -> TyConSet -> TyConSet
intersectTyConSet = intersectUniqSets

intersectsTyConSet :: TyConSet -> TyConSet -> Bool
intersectsTyConSet s1 s2 = not (isEmptyTyConSet (s1 `intersectTyConSet` s2))

nameSetAny :: (TyCon (TyVar KiVar) KiVar -> Bool) -> TyConSet -> Bool
nameSetAny = uniqSetAny

nameSetAll :: (TyCon (TyVar KiVar) KiVar -> Bool) -> TyConSet -> Bool
nameSetAll = uniqSetAll
