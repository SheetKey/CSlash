module CSlash.Types.Var.Set where

import CSlash.Types.Var ( Var, TypeVar, KindVar, Id )
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

type KdVarSet = UniqSet KindVar

type KiVarSet = UniqSet KindVar

emptyVarSet :: VarSet
emptyVarSet = emptyUniqSet

extendVarSet :: VarSet -> Var -> VarSet
extendVarSet = addOneToUniqSet

elemVarSet :: Var -> VarSet -> Bool
elemVarSet = elementOfUniqSet

minusVarSet :: VarSet -> VarSet -> VarSet
minusVarSet = minusUniqSet

isEmptyVarSet :: VarSet -> Bool
isEmptyVarSet = isEmptyUniqSet

subVarSet :: VarSet -> VarSet -> Bool
subVarSet s1 s2 = isEmptyVarSet (s1 `minusVarSet` s2)

pprVarSet :: VarSet -> ([Var] -> SDoc) -> SDoc
pprVarSet = pprUFM . getUniqSet

type DVarSet = UniqDSet Var

type DKiVarSet = UniqDSet KindVar

emptyDVarSet :: DVarSet
emptyDVarSet = emptyUniqDSet

extendDVarSet :: DVarSet -> Var -> DVarSet 
extendDVarSet = addOneToUniqDSet

elemDVarSet :: Var -> DVarSet -> Bool
elemDVarSet = elementOfUniqDSet

dVarSetToVarSet :: DVarSet -> VarSet
dVarSetToVarSet = unsafeUFMToUniqSet . udfmToUfm . getUniqDSet
