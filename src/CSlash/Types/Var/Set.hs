module CSlash.Types.Var.Set where

import CSlash.Types.Var
  ( Var
  , TyVar, TcTyVar, AnyTyVar
  , KiVar, TcKiVar, AnyKiVar
  , KiCoVar, Id )
import CSlash.Types.Unique
import CSlash.Types.Name ( Name )
import CSlash.Types.Unique.Set
import CSlash.Types.Unique.DSet
import CSlash.Types.Unique.FM ( disjointUFM, pluralUFM, pprUFM )
import CSlash.Types.Unique.DFM ( disjointUDFM, udfmToUfm, anyUDFM, allUDFM )
import CSlash.Utils.Outputable (SDoc)

type MkVarSet = UniqSet

type VarSet tv kv = MkVarSet (Var tv kv)

type IdSet tv kv = MkVarSet (Id tv kv)

type TyVarSet kv = MkVarSet (TyVar kv)
type TcTyVarSet kv = MkVarSet (TcTyVar kv)
type AnyTyVarSet kv = MkVarSet (AnyTyVar kv)

type KiVarSet = MkVarSet KiVar
type TcKiVarSet = MkVarSet TcKiVar
type AnyKiVarSet = MkVarSet AnyKiVar

emptyVarSet :: UniqSet a
emptyVarSet = emptyUniqSet

unitVarSet :: Uniquable a => a -> UniqSet a
unitVarSet = unitUniqSet

extendVarSet :: Uniquable a => UniqSet a -> a -> UniqSet a
extendVarSet = addOneToUniqSet

extendVarSetList :: Uniquable a => UniqSet a -> [a] -> UniqSet a
extendVarSetList = addListToUniqSet

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

disjointVarSet :: UniqSet a -> UniqSet a -> Bool
disjointVarSet s1 s2 = disjointUFM (getUniqSet s1) (getUniqSet s2)

subVarSet :: UniqSet a -> UniqSet a -> Bool
subVarSet s1 s2 = isEmptyVarSet (s1 `minusVarSet` s2)

lookupVarSet :: Uniquable a => UniqSet a -> a -> Maybe a
lookupVarSet = lookupUniqSet

anyVarSet :: (a -> Bool) -> UniqSet a -> Bool
anyVarSet = uniqSetAny

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

type MkDVarSet = UniqDSet

type DVarSet tv kv = MkDVarSet (Var tv kv)

type DKiVarSet = MkDVarSet KiVar
type DTcKiVarSet = MkDVarSet TcKiVar
type DAnyKiVarSet = MkDVarSet AnyKiVar

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
