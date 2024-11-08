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
import GHC.Stack (callStack)

import CSlash.Utils.Misc

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

data SkolemInfo = SkolemInfo Unique SkolemInfoAnon

data SkolemInfoAnon
  = SigSkol UserTypeCtxt TcType [(Name, TcTyVar)]
  | SigTypeSkol UserTypeCtxt
  | ForAllSkol TyVarBndrs
  | InferSkol [(Name, TcType)]
  | UnifyForAllSkol TcType
  | TyConSkol (TyConFlavor TyCon) Name
  | UnkSkol CallStack

unkSkol :: HasDebugCallStack => SkolemInfo
unkSkol = SkolemInfo (mkUniqueGrimily 0) unkSkolAnon

unkSkolAnon :: HasDebugCallStack => SkolemInfoAnon
unkSkolAnon = UnkSkol callStack

data TyVarBndrs = CsTyVarBndrsRn [CsTyVarBndr Rn]

instance Outputable TyVarBndrs where
  ppr (CsTyVarBndrsRn bndrs) = fsep (map ppr bndrs)
