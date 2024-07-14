module CSlash.Tc.Types.Origin where

import CSlash.Tc.Utils.TcType

import CSlash.Types.Name
import CSlash.Types.Name.Reader
import CSlash.Types.Basic
import CSlash.Types.SrcLoc

import CSlash.Data.FastString

data UserTypeCtxt
  = FunSigCtxt Name ReportRedundantConstraints
  | InfSigCtxt Name
  | ExprSigCtxt ReportRedundantConstraints
  | KindSigCtxt
  | TypeAppCtxt
  | ConArgCtxt Name
  | TySynCtxt Name
  | GenSigCtxt
  | SigmaCtxt
  | TyVarBndrKindCtxt name
  deriving (Eq)

data ReportRedundantConstraints
  = NoRRC
  | WantRRC SrcSpan
  deriving (Eq)

data SkolemInfo = SkolemInfor Unique SkolemInfoAnon

data SkolemInfoAnon
  = SigSkol UserTypeCtx TcType [(Name, TcTyVar)]
  | SigTypeSkol UserTypeCtxt
  | ForAllSkol TyVarBndrs
  | InferSkol [(Name, TcType)]
  | UnifyForAllSkol TcType
  | TyConSkol (TyConFlavor TyCon) Name
  | UnkSkol CallStack
