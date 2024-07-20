module CSlash.Types.Id.Make where

import CSlash.Builtin.Types.Prim
import CSlash.Builtin.Types
import CSlash.Builtin.Names

import CSlash.Core.Type
import CSlash.Core.TyCo.Rep
import CSlash.Core.TyCon
import CSlash.Core.DataCon

import CSlash.Types.SourceText
import CSlash.Types.RepType (countFunRepArgs)
import CSlash.Types.Name.Set
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Id
import CSlash.Types.Id.Info
import CSlash.Types.Basic hiding ( SuccessFlag(..) )
import CSlash.Types.Var (VarBndr(Bndr), visArgConstraintLike, tyVarName)

import CSlash.Tc.Types.Origin
import CSlash.Tc.Utils.TcType as TcType

import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import CSlash.Data.FastString

{- *********************************************************************
*                                                                      *
        Data constructors
*                                                                      *
********************************************************************* -}

-- needs to change if I add newtypes
mkDataConWorkId :: Name -> DataCon -> Id
mkDataConWorkId wkr_name data_con
  = mkGlobalId (DataConWorkId data_con) wkr_name wkr_ty 
  where
    wkr_ty = dataConType data_con
    alg_wkr_info = noCafIdInfo
                   `setArityInfo` wkr_arity
                   `setUnfoldingInfo` evalUnfolding
                   `setLFInfo` wkr_lf_info
    wkr_arity = dataConArity data_con
    wkr_lf_info
      | wkr_arity == 0 = LFCon data_con
      | otherwise = LFReEntrant TopLevel (countFunRepArgs wkr_arity wkr_ty) True ArgUnknown
