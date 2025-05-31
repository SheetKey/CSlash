module CSlash.Types.Var.Set where

import CSlash.Types.Var ( Var, TypeVar, KindVar, KiCoVar, Id )
import CSlash.Types.Unique
import CSlash.Types.Name ( Name )
import CSlash.Types.Unique.Set
import CSlash.Types.Unique.DSet
import CSlash.Types.Unique.FM ( disjointUFM, pluralUFM, pprUFM )
import CSlash.Types.Unique.DFM ( disjointUDFM, udfmToUfm, anyUDFM, allUDFM )
import CSlash.Utils.Outputable (SDoc)

type VarSet = UniqSet Var

type IdSet = UniqSet Id

type TyVarSet = UniqSet TypeVar

type KiVarSet = UniqSet KindVar

type KiCoVarSet = UniqSet KiCoVar

type TyKiVarSet = UniqSet Var

emptyVarSet :: VarSet
emptyVarSet = emptyUniqSet

unitVarSet :: Var -> VarSet
unitVarSet = unitUniqSet

extendVarSet :: VarSet -> Var -> VarSet
extendVarSet = addOneToUniqSet

extendVarSetList :: VarSet -> [Var] -> VarSet
extendVarSetList = addListToUniqSet

elemVarSet :: Var -> VarSet -> Bool
elemVarSet = elementOfUniqSet

minusVarSet :: VarSet -> VarSet -> VarSet
minusVarSet = minusUniqSet

delVarSetList :: VarSet -> [Var] -> VarSet
delVarSetList = delListFromUniqSet

isEmptyVarSet :: VarSet -> Bool
isEmptyVarSet = isEmptyUniqSet

mkVarSet :: [Var] -> VarSet
mkVarSet = mkUniqSet

disjointVarSet :: VarSet -> VarSet -> Bool
disjointVarSet s1 s2 = disjointUFM (getUniqSet s1) (getUniqSet s2)

subVarSet :: VarSet -> VarSet -> Bool
subVarSet s1 s2 = isEmptyVarSet (s1 `minusVarSet` s2)

lookupVarSet :: VarSet -> Var -> Maybe Var
lookupVarSet = lookupUniqSet

anyVarSet :: (Var -> Bool) -> VarSet -> Bool
anyVarSet = uniqSetAny

unionVarSet :: VarSet -> VarSet -> VarSet
unionVarSet = unionUniqSets

unionVarSets :: [VarSet] -> VarSet
unionVarSets = unionManyUniqSets

transCloVarSet :: (VarSet -> VarSet) -> VarSet -> VarSet
transCloVarSet fn seeds = go seeds seeds
  where
    go acc candidates
      | isEmptyVarSet new_vs = acc
      | otherwise = go (acc `unionVarSet` new_vs) new_vs
      where
        new_vs = fn candidates `minusVarSet` acc

pprVarSet :: VarSet -> ([Var] -> SDoc) -> SDoc
pprVarSet = pprUFM . getUniqSet

type DVarSet = UniqDSet Var

type DKiVarSet = UniqDSet KindVar

emptyDVarSet :: DVarSet
emptyDVarSet = emptyUniqDSet

mkDVarSet :: [Var] -> DVarSet
mkDVarSet = mkUniqDSet

extendDVarSet :: DVarSet -> Var -> DVarSet 
extendDVarSet = addOneToUniqDSet

elemDVarSet :: Var -> DVarSet -> Bool
elemDVarSet = elementOfUniqDSet

dVarSetElems :: DVarSet -> [Var]
dVarSetElems = uniqDSetToList

isEmptyDVarSet :: DVarSet -> Bool
isEmptyDVarSet = isEmptyUniqDSet

nonDetStrictFoldDVarSet :: (Var -> a -> a) -> a -> DVarSet -> a
nonDetStrictFoldDVarSet = nonDetStrictFoldUniqDSet

delDVarSetList :: DVarSet -> [Var] -> DVarSet
delDVarSetList = delListFromUniqDSet

dVarSetToVarSet :: DVarSet -> VarSet
dVarSetToVarSet = unsafeUFMToUniqSet . udfmToUfm . getUniqDSet
