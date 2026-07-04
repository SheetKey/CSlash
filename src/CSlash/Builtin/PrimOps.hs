{-# LANGUAGE OverloadedStrings #-}

module CSlash.Builtin.PrimOps where

import CSlash.Cs.Pass

-- import {-# SOURCE #-} CSlash.Core.Opt.ConstantFold (primOpRules)
import CSlash.Core.Opt.ConstantFold (primOpRules)
import CSlash.Core.FVs (mkRuleInfo)

import CSlash.Builtin.Types.Prim
import CSlash.Builtin.Types
import CSlash.Builtin.Uniques (mkPrimOpIdUnique{-, mkPrimOpWrapperUnique-} )
import CSlash.Builtin.Names ( cSLASH_PRIM )

-- import CSlash.Core.TyCon    ( isPrimTyCon, isUnboxedTupleTyCon, PrimRep(..) )
import CSlash.Core.Type
import CSlash.Core.Type.Rep
import CSlash.Core.Kind

import CSlash.Pir.Type

import CSlash.Types.Demand
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.Var.Class
import CSlash.Types.TyThing
import CSlash.Types.Name
-- import GHC.Types.RepType ( tyConPrimRep )
import CSlash.Types.Basic
import CSlash.Types.Fixity ( Fixity(..), FixityDirection(..) )
import CSlash.Types.SrcLoc ( wiredInSrcSpan )
-- import GHC.Types.ForeignCall ( CLabelString )
import CSlash.Types.Unique ( Unique )

import CSlash.Unit.Types ( Unit )

import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Trace

import CSlash.Data.FastString
import Data.List( inits )
import Data.Maybe ( mapMaybe, listToMaybe, catMaybes, maybeToList )

data PrimOp
  -- Casts
  = IntToInt Int Int
  | IntToUInt Int Int
  | UIntToInt Int Int
  | UIntToUInt Int Int
  | DoubleToFloatOp 
  | FloatToDoubleOp 
  | Int64ToAddrOp
  | AddrToInt64Op

  -- IO
  | ReturnIO
  | BindIO
  deriving Eq

instance Enum PrimOp where
  fromEnum op = case op of
    IntToInt i1 i2 -> assert (i1 <= 128) $
                      assert (i2 <= 128) $
                      0 + (i1 * i2)
    IntToUInt i1 i2 -> assert (i1 <= 128) $
                       assert (i2 <= 128) $
                       (128 * 128) + 1 + (i1 * i2)
    UIntToInt i1 i2 -> assert (i1 <= 128) $
                       assert (i2 <= 128) $
                       (2 * (128 * 128)) + 2 + (i1 * i2)
    UIntToUInt i1 i2 -> assert (i1 <= 128) $
                        assert (i2 <= 128) $
                        (3 * (128 * 128)) + 3 + (i1 * i2)
    DoubleToFloatOp -> (4 * (128 * 128)) + 4
    FloatToDoubleOp -> (4 * (128 * 128)) + 5
    Int64ToAddrOp -> (4 * (128 * 128)) + 6
    AddrToInt64Op -> (4 * (128 * 128)) + 7

    ReturnIO -> (4 * (128 * 128)) + 8
    BindIO -> (4 * (128 * 128)) + 9

data PrimOpInfo = PrimOpInfo
  PrimOpId
  PrimOpEffect
  PrimOpImpl
  PrimOpCommutable
  PrimOpCodeSize
  PrimOpWorkFree
  PrimOpCheap
  PrimOpFixity

type PrimOpId = Id Zk

data PrimOpEffect
  = NoEffect
  | CanFail
  | ThrowsException
  | ReadWriteEffect
  deriving (Eq, Ord)

data PrimOpImpl = POI_Pir | POI_LLVM
  deriving Eq

type PrimOpCommutable = Bool

type PrimOpCodeSize = Int

type PrimOpWorkFree = Bool

type PrimOpCheap = Bool

type PrimOpFixity = Maybe Fixity

primOpInfo :: PrimOp -> PrimOpInfo
primOpInfo op = case op of
  -- Casts

  -- IO
  ReturnIO -> PrimOpInfo (mkPrimOpId op) NoEffect POI_Pir False 0 True True Nothing

  _ -> panic "primOpInfo"

data PrimOpIdInfo
  = GenPrimOpIdInfo
    OccName
    [KiVar Zk]
    [(MonoKind Zk, KiPredCon, MonoKind Zk)]
    [TyVar Zk]
    [Type Zk]
    (Type Zk)

primOpIdInfo :: PrimOp -> PrimOpIdInfo
primOpIdInfo op = case op of
  -- Casts

  -- IO
  ReturnIO -> let (a_kv, r_kv) = case mkTemplateKindVarsRes 1 of
                                   ([a_kv], r_kv) -> (a_kv, r_kv)
                                   _ -> panic "unreachable"
                  a_ki = KiVarKi a_kv
                  r_ki = KiVarKi r_kv
                  pred = [(a_ki, LTEQKi, r_ki)]
                  a_tv = case mkTemplateTyVars [a_ki] of
                           [a_tv] -> a_tv
                           _ -> panic "unreachable"
                  a_ty = TyVarTy a_tv
                  res_ty = mkTyConApp ioTyCon [Embed a_ki, Embed r_ki, a_ty]
              in GenPrimOpIdInfo (mkVarOccFS "return_io") [a_kv, r_kv] pred [a_tv] [a_ty] res_ty

  _ -> panic "primOpIdInfo"

mkPrimOpId :: PrimOp -> PrimOpId
mkPrimOpId prim_op = case primOpIdInfo prim_op of
  GenPrimOpIdInfo occ kvs in_preds tvs args res ->
    let fun_kvs = tail $ mkTemplateFunKindVars (length args)
        fun_kis = BIKi UKd : (KiVarKi <$> fun_kvs)
        arg_kis = typeMonoKind <$> args
        fun_preds = let want_lts = inits arg_kis
                    in assert (length want_lts - 1 == length fun_kis) $
                       concat $ zipWith (fmap . (KiPredApp LTEQKi)) fun_kis want_lts

        kcvs = mkTemplateKiCoVars (map mk_pred in_preds ++ fun_preds)
        ty = mkBigLamTys kvs $
             mkForAllKiCos kcvs $
             mkInfForAllTys tvs $
             mkFunTys args fun_kis res
        name = mkWiredInName cSLASH_PRIM occ (mkPrimOpIdUnique (fromEnum prim_op))
               (AnId id) UserSyntax
        id = mkGlobalId (PrimOpId prim_op) name ty info

        info = noCafIdInfo
               `setRuleInfo` mkRuleInfo (maybeToList $ primOpRules name prim_op)
               `setArityInfo` 1
               `setDmdSigInfo` mkClosedDmdSig (replicate 1 topDmd) topDiv
               `setInlinePragInfo` neverInlinePragma
    in pprTrace "mkPrimOpId" (ppr id) id
  where
    mk_pred :: (MonoKind Zk, KiPredCon, MonoKind Zk) -> MonoKind Zk
    mk_pred (kl, pred, kr) = KiPredApp pred kl kr

primOpOkForSpeculation :: PrimOp -> Bool
primOpOkForSpeculation op
  = primOpEffect op == NoEffect && not (primOpImpl op == POI_Pir)

primOpOkToDiscard :: PrimOp -> Bool
primOpOkToDiscard op
  = primOpEffect op < ThrowsException

primOpIsWorkFree :: PrimOp -> Bool
primOpIsWorkFree op = case primOpInfo op of
  PrimOpInfo _ _ _ _ _ f _ _ -> f

primOpIsCheap :: PrimOp -> Bool
primOpIsCheap op = case primOpInfo op of
  PrimOpInfo _ _ _ _ _ _ c _ -> c

primOpEffect :: PrimOp -> PrimOpEffect
primOpEffect op = case primOpInfo op of
  PrimOpInfo _ e _ _ _ _ _ _ -> e

primOpImpl :: PrimOp -> PrimOpImpl
primOpImpl op = case primOpInfo op of
  PrimOpInfo _ _ i _ _ _ _ _ -> i

primOpIsDiv :: PrimOp -> Bool
primOpIsDiv op = panic "primOpIsDiv"
