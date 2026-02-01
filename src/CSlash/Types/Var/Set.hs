module CSlash.Types.Var.Set where

import CSlash.Types.Var
  ( TyVar, TcTyVar, TyCoVar
  , KiVar, TcKiVar, KiCoVar
  , Id )
import CSlash.Types.Unique
import CSlash.Types.Name ( Name )
import CSlash.Types.Unique.Set
import CSlash.Types.Unique.DSet
import CSlash.Types.Unique.FM ( disjointUFM, pluralUFM, pprUFM )
import CSlash.Types.Unique.DFM ( disjointUDFM, udfmToUfm, anyUDFM, allUDFM )
import CSlash.Utils.Outputable (SDoc)

type VarSet = UniqSet

type IdSet p = VarSet (Id p)

type TyVarSet p = VarSet (TyVar p)
type TcTyVarSet = VarSet TcTyVar

type KiVarSet p = VarSet (KiVar p)
type TcKiVarSet = VarSet TcKiVar

type TyCoVarSet p = VarSet (TyCoVar p)

type KiCoVarSet p = VarSet (KiCoVar p)

emptyVarSet :: UniqSet a
emptyVarSet = emptyUniqSet

unitVarSet :: Uniquable a => a -> UniqSet a
unitVarSet = unitUniqSet

extendVarSet :: Uniquable a => UniqSet a -> a -> UniqSet a
extendVarSet = addOneToUniqSet

extendVarSetList :: Uniquable a => UniqSet a -> [a] -> UniqSet a
extendVarSetList = addListToUniqSet

intersectVarSet :: UniqSet a -> UniqSet a -> UniqSet a
intersectVarSet = intersectUniqSets

elemVarSet :: Uniquable a => a -> UniqSet a -> Bool
elemVarSet = elementOfUniqSet

minusVarSet :: UniqSet a -> UniqSet a -> UniqSet a
minusVarSet = minusUniqSet

delVarSetList :: Uniquable a => UniqSet a -> [a] -> UniqSet a
delVarSetList = delListFromUniqSet

isEmptyVarSet :: UniqSet a -> Bool
isEmptyVarSet = isEmptyUniqSet

mkVarSet :: Uniquable a => [a] -> UniqSet a
mkVarSet = mkUniqSet

intersectsVarSet :: UniqSet a -> UniqSet a -> Bool
intersectsVarSet s1 s2 = not (s1 `disjointVarSet` s2)

disjointVarSet :: UniqSet a -> UniqSet a -> Bool
disjointVarSet s1 s2 = disjointUFM (getUniqSet s1) (getUniqSet s2)

subVarSet :: UniqSet a -> UniqSet a -> Bool
subVarSet s1 s2 = isEmptyVarSet (s1 `minusVarSet` s2)

lookupVarSet :: Uniquable a => UniqSet a -> a -> Maybe a
lookupVarSet = lookupUniqSet

lookupVarSet_Directly :: UniqSet a -> Unique -> Maybe a 
lookupVarSet_Directly = lookupUniqSet_Directly

anyVarSet :: (a -> Bool) -> UniqSet a -> Bool
anyVarSet = uniqSetAny

mapVarSet :: Uniquable b => (a -> b) -> UniqSet a -> UniqSet b
mapVarSet = mapUniqSet

nonDetStrictFoldVarSet :: (a -> b -> b) -> b -> UniqSet a -> b
nonDetStrictFoldVarSet = nonDetStrictFoldUniqSet

unionVarSet :: UniqSet a -> UniqSet a -> UniqSet a
unionVarSet = unionUniqSets

unionVarSets :: [UniqSet a] -> UniqSet a
unionVarSets = unionManyUniqSets

transCloVarSet :: (UniqSet a -> UniqSet a) -> UniqSet a -> UniqSet a
transCloVarSet fn seeds = go seeds seeds
  where
    go acc candidates
      | isEmptyVarSet new_vs = acc
      | otherwise = go (acc `unionVarSet` new_vs) new_vs
      where
        new_vs = fn candidates `minusVarSet` acc

pprVarSet :: UniqSet a -> ([a] -> SDoc) -> SDoc
pprVarSet = pprUFM . getUniqSet

type DVarSet = UniqDSet

type DKiVarSet p = DVarSet (KiVar p)
type DTcKiVarSet = DVarSet TcKiVar

type DTyVarSet p = DVarSet (TyVar p)
type DTcTyVarSet = DVarSet TcTyVar

type DKiCoVarSet p = DVarSet (KiCoVar p)

emptyDVarSet :: UniqDSet a
emptyDVarSet = emptyUniqDSet

mkDVarSet :: Uniquable a => [a] -> UniqDSet a
mkDVarSet = mkUniqDSet

extendDVarSet :: Uniquable a => UniqDSet a -> a -> UniqDSet a
extendDVarSet = addOneToUniqDSet

elemDVarSet :: Uniquable a => a -> UniqDSet a -> Bool
elemDVarSet = elementOfUniqDSet

dVarSetElems :: UniqDSet a -> [a]
dVarSetElems = uniqDSetToList

isEmptyDVarSet :: UniqDSet a -> Bool
isEmptyDVarSet = isEmptyUniqDSet

nonDetStrictFoldDVarSet :: (a -> b -> b) -> b -> UniqDSet a -> b
nonDetStrictFoldDVarSet = nonDetStrictFoldUniqDSet

partitionDVarSet :: (a -> Bool) -> UniqDSet a -> (UniqDSet a, UniqDSet a)
partitionDVarSet = partitionUniqDSet

delDVarSetList :: Uniquable a => UniqDSet a -> [a] -> UniqDSet a
delDVarSetList = delListFromUniqDSet

dVarSetToVarSet :: UniqDSet a -> UniqSet a
dVarSetToVarSet = unsafeUFMToUniqSet . udfmToUfm . getUniqDSet
