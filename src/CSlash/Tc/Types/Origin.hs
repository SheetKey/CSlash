{-# LANGUAGE DataKinds #-}

module CSlash.Tc.Types.Origin where

import CSlash.Tc.Utils.TcType

import CSlash.Cs

import CSlash.Core.TyCon

import CSlash.Types.Id
import CSlash.Types.Name
import CSlash.Types.Name.Reader
import CSlash.Types.Basic
import CSlash.Types.SrcLoc

import CSlash.Data.FastString

import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Types.Unique

import GHC.Exception

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
  | TyVarBndrKindCtxt Name
  deriving (Eq)

data ReportRedundantConstraints
  = NoRRC
  | WantRRC SrcSpan
  deriving (Eq)

data SkolemInfo = SkolemInfor Unique SkolemInfoAnon

data SkolemInfoAnon
  = SigSkol UserTypeCtxt TcType [(Name, TcTyVar)]
  | SigTypeSkol UserTypeCtxt
  | ForAllSkol TyVarBndrs
  | InferSkol [(Name, TcType)]
  | UnifyForAllSkol TcType
  | TyConSkol (TyConFlavor TyCon) Name
  | UnkSkol CallStack

data TyVarBndrs = CsTyVarBndrsRn [CsTyVarBndr Rn]

instance Outputable TyVarBndrs where
  ppr (CsTyVarBndrsRn bndrs) = fsep (map ppr bndrs)
