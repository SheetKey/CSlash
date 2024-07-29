module CSlash.Types.Var.Set where

import CSlash.Types.Var ( Var, TyVar, CoVar, TyCoVar, Id )
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

emptyVarSet :: VarSet
emptyVarSet = emptyUniqSet
