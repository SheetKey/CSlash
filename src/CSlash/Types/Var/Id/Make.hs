module CSlash.Types.Var.Id.Make where

import CSlash.Cs.Pass

import CSlash.Builtin.Types.Prim
import CSlash.Builtin.Types
import CSlash.Builtin.Names

import CSlash.Core
import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Core.Type.Rep
import CSlash.Core.TyCon
import CSlash.Core.DataCon
import CSlash.Core.Unfold.Make

import CSlash.Types.SourceText
import CSlash.Types.RepType (countFunRepArgs)
import CSlash.Types.Name.Set
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.Basic hiding ( SuccessFlag(..) )
import CSlash.Types.Var (VarBndr(Bndr), varName)

import CSlash.Tc.Types.Origin
import CSlash.Tc.Utils.TcType as TcType

import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import CSlash.Data.FastString

{- *********************************************************************
*                                                                      *
        Wired in Ids
*                                                                      *
********************************************************************* -}

wiredInIds :: [Id Zk]
wiredInIds
  = magicIds
  ++ csPrimIds
  ++ errorIds

magicIds :: [Id Zk]
magicIds = []

csPrimIds :: [Id Zk]
csPrimIds =
  [
    voidPrimId
  ]

errorIds :: [Id Zk]
errorIds = []

{- *********************************************************************
*                                                                      *
        Data constructors
*                                                                      *
********************************************************************* -}

-- needs to change if I add newtypes
mkDataConId :: Name -> DataCon Zk -> Id Zk
mkDataConId wkr_name data_con
  = mkGlobalId (DataConId data_con) wkr_name wkr_ty alg_wkr_info
  where
    wkr_ty = dataConType data_con
    alg_wkr_info = noCafIdInfo
                   `setArityInfo` wkr_arity
                   `setUnfoldingInfo` evaldUnfolding
                   `setLFInfo` wkr_lf_info
    wkr_arity = dataConArity data_con
    wkr_lf_info
      | wkr_arity == 0 = LFCon data_con
      | otherwise = LFReEntrant TopLevel (countFunRepArgs wkr_arity wkr_ty) True ArgUnknown

{- *********************************************************************
*                                                                      *
              Un-definable
*                                                                      *
********************************************************************* -}

leftSectionName :: Name
leftSectionName = panic "leftSectionName"

rightSectionName :: Name
rightSectionName = panic "rightSectionName"

leftTySectionName :: Name
leftTySectionName = panic "leftTySectionName"

rightTySectionName :: Name
rightTySectionName = panic "rightTySectionName"

voidPrimIdName :: Name
voidPrimIdName = mkWiredInIdName cSLASH_BUILTIN (fsLit "void#") voidPrimIdKey voidPrimId

voidPrimId :: CoreId
voidPrimId = mkVanillaGlobalWithInfo
             voidPrimIdName
             (mkTyConApp unitTyCon [Embed (BIKi UKd)])
             (vanillaIdInfo `setUnfoldingInfo` mkCompulsoryUnfolding (unitExpr (BIKi UKd)))

unitExpr :: CoreMonoKind -> CoreExpr
unitExpr ki = App (Var (dataConId unitDataCon)) (Kind ki)

voidArgId :: CoreId
voidArgId = mkSysLocal (fsLit "void") voidArgIdKey (mkTyConApp unitTyCon [Embed (BIKi UKd)])
