{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -O0 #-}

module CSlash.Cs.Instances where

import Data.Data hiding (Fixity)

import CSlash.Cs.Extension
import CSlash.Cs.Binds
import CSlash.Cs.Decls
import CSlash.Cs.Expr
import CSlash.Cs.Lit
import CSlash.Cs.Type
import CSlash.Cs.Kind
import CSlash.Cs.Pat
import CSlash.Cs.ImpExp
import CSlash.Parser.Annotation

instance Data (CsLocalBindsLR Ps Ps)
instance Data (CsLocalBindsLR Ps Rn)
instance Data (CsLocalBindsLR Rn Rn)
instance Data (CsLocalBindsLR Tc Tc)
instance Data (CsLocalBindsLR Zk Zk)

deriving instance Data (CsValBindsLR Ps Ps)
deriving instance Data (CsValBindsLR Ps Rn)
deriving instance Data (CsValBindsLR Rn Rn)
deriving instance Data (CsValBindsLR Tc Tc)
deriving instance Data (CsValBindsLR Zk Zk)

deriving instance Data (NCsValBindsLR Ps)
deriving instance Data (NCsValBindsLR Rn)
deriving instance Data (NCsValBindsLR Tc)
deriving instance Data (NCsValBindsLR Zk)

deriving instance Data (CsBindLR Ps Ps)
deriving instance Data (CsBindLR Ps Rn)
deriving instance Data (CsBindLR Rn Rn)
deriving instance Data (CsBindLR Tc Tc)
deriving instance Data (CsBindLR Zk Zk)

deriving instance Data (AbsBinds Tc)
deriving instance Data (AbsBinds Zk)

deriving instance Data (ABExport Tc)
deriving instance Data (ABExport Zk)

deriving instance Data (Sig Ps)
deriving instance Data (Sig Rn)
deriving instance Data (Sig Tc)
deriving instance Data (Sig Zk)

deriving instance Data (FixitySig Ps)
deriving instance Data (FixitySig Rn)
deriving instance Data (FixitySig Tc)
deriving instance Data (FixitySig Zk)

deriving instance Data (CsDecl Ps)
deriving instance Data (CsDecl Rn)
deriving instance Data (CsDecl Tc)
deriving instance Data (CsDecl Zk)

deriving instance Data (CsGroup Ps)
deriving instance Data (CsGroup Rn)
deriving instance Data (CsGroup Tc)
deriving instance Data (CsGroup Zk)

deriving instance Data (TypeGroup Ps)
deriving instance Data (TypeGroup Rn)
deriving instance Data (TypeGroup Tc)
deriving instance Data (TypeGroup Zk)

deriving instance Data (CsExpr Ps)
deriving instance Data (CsExpr Rn)
deriving instance Data (CsExpr Tc)
deriving instance Data (CsExpr Zk)

deriving instance Data (CsTupArg Ps)
deriving instance Data (CsTupArg Rn)
deriving instance Data (CsTupArg Tc)
deriving instance Data (CsTupArg Zk)

deriving instance Data (MatchGroup Ps (LocatedA (CsExpr Ps)))
deriving instance Data (MatchGroup Rn (LocatedA (CsExpr Rn)))
deriving instance Data (MatchGroup Tc (LocatedA (CsExpr Tc)))
deriving instance Data (MatchGroup Zk (LocatedA (CsExpr Zk)))

deriving instance Data (MatchGroup Ps (LocatedA (CsType Ps)))
deriving instance Data (MatchGroup Rn (LocatedA (CsType Rn)))
deriving instance Data (MatchGroup Tc (LocatedA (CsType Tc)))
deriving instance Data (MatchGroup Zk (LocatedA (CsType Zk)))

deriving instance Data (Match Ps (LocatedA (CsExpr Ps)))
deriving instance Data (Match Rn (LocatedA (CsExpr Rn)))
deriving instance Data (Match Tc (LocatedA (CsExpr Tc)))
deriving instance Data (Match Zk (LocatedA (CsExpr Zk)))

deriving instance Data (Match Ps (LocatedA (CsType Ps)))
deriving instance Data (Match Rn (LocatedA (CsType Rn)))
deriving instance Data (Match Tc (LocatedA (CsType Tc)))
deriving instance Data (Match Zk (LocatedA (CsType Zk)))

deriving instance Data (GRHSs Ps (LocatedA (CsExpr Ps)))
deriving instance Data (GRHSs Rn (LocatedA (CsExpr Rn)))
deriving instance Data (GRHSs Tc (LocatedA (CsExpr Tc)))
deriving instance Data (GRHSs Zk (LocatedA (CsExpr Zk)))

deriving instance Data (GRHSs Ps (LocatedA (CsType Ps)))
deriving instance Data (GRHSs Rn (LocatedA (CsType Rn)))
deriving instance Data (GRHSs Tc (LocatedA (CsType Tc)))
deriving instance Data (GRHSs Zk (LocatedA (CsType Zk)))

deriving instance Data (GRHS Ps (LocatedA (CsExpr Ps)))
deriving instance Data (GRHS Rn (LocatedA (CsExpr Rn)))
deriving instance Data (GRHS Tc (LocatedA (CsExpr Tc)))
deriving instance Data (GRHS Zk (LocatedA (CsExpr Zk)))

deriving instance Data (GRHS Ps (LocatedA (CsType Ps)))
deriving instance Data (GRHS Rn (LocatedA (CsType Rn)))
deriving instance Data (GRHS Tc (LocatedA (CsType Tc)))
deriving instance Data (GRHS Zk (LocatedA (CsType Zk)))

deriving instance Data (StmtLR Ps Ps (LocatedA (CsExpr Ps)))
deriving instance Data (StmtLR Ps Rn (LocatedA (CsExpr Rn)))
deriving instance Data (StmtLR Rn Rn (LocatedA (CsExpr Rn)))
deriving instance Data (StmtLR Tc Tc (LocatedA (CsExpr Tc)))
deriving instance Data (StmtLR Zk Zk (LocatedA (CsExpr Zk)))

deriving instance Data fn => Data (CsStmtContext fn)
deriving instance Data fn => Data (CsMatchContext fn)

deriving instance Data SyntaxExprRn
deriving instance Data SyntaxExprTc
deriving instance Data SyntaxExprZk

deriving instance Data (CsLit Ps)
deriving instance Data (CsLit Rn)
deriving instance Data (CsLit Tc)
deriving instance Data (CsLit Zk)

deriving instance Data (CsOverLit Ps)
deriving instance Data (CsOverLit Rn)
deriving instance Data (CsOverLit Tc)
deriving instance Data (CsOverLit Zk)

deriving instance Data OverLitRn
deriving instance Data OverLitTc

deriving instance Data (Pat Ps)
deriving instance Data (Pat Rn)
deriving instance Data (Pat Tc)
deriving instance Data (Pat Zk)

deriving instance Data ConPatTc

deriving instance Data (CsConPatTyArg Ps)
deriving instance Data (CsConPatTyArg Rn)
deriving instance Data (CsConPatTyArg Tc)
deriving instance Data (CsConPatTyArg Zk)

deriving instance Data (CsSigType Ps)
deriving instance Data (CsSigType Rn)
deriving instance Data (CsSigType Tc)
deriving instance Data (CsSigType Zk)

deriving instance Data (CsPatSigType Ps)
deriving instance Data (CsPatSigType Rn)
deriving instance Data (CsPatSigType Tc)
deriving instance Data (CsPatSigType Zk)

deriving instance Data (CsPatSigKind Ps)
deriving instance Data (CsPatSigKind Rn)
deriving instance Data (CsPatSigKind Tc)
deriving instance Data (CsPatSigKind Zk)

deriving instance Data (CsTyPat Ps)
deriving instance Data (CsTyPat Rn)
deriving instance Data (CsTyPat Tc)
deriving instance Data (CsTyPat Zk)

deriving instance Data (CsForAllTelescope Ps)
deriving instance Data (CsForAllTelescope Rn)
deriving instance Data (CsForAllTelescope Tc)
deriving instance Data (CsForAllTelescope Zk)

deriving instance Data (CsTyVarBndr Ps)
deriving instance Data (CsTyVarBndr Rn)
deriving instance Data (CsTyVarBndr Tc)
deriving instance Data (CsTyVarBndr Zk)

deriving instance Data (CsType Ps)
deriving instance Data (CsType Rn)
deriving instance Data (CsType Tc)
deriving instance Data (CsType Zk)

deriving instance Data (CsTyTupArg Ps)
deriving instance Data (CsTyTupArg Rn)
deriving instance Data (CsTyTupArg Tc)
deriving instance Data (CsTyTupArg Zk)

deriving instance Data (CsKind Ps)
deriving instance Data (CsKind Rn)
deriving instance Data (CsKind Tc)
deriving instance Data (CsKind Zk)

deriving instance Data (CsKdRel Ps)
deriving instance Data (CsKdRel Rn)
deriving instance Data (CsKdRel Tc)
deriving instance Data (CsKdRel Zk)

deriving instance Data (CsArrow Ps)
deriving instance Data (CsArrow Rn)
deriving instance Data (CsArrow Tc)
deriving instance Data (CsArrow Zk)

deriving instance Data (ImportDecl Ps)
deriving instance Data (ImportDecl Rn)
deriving instance Data (ImportDecl Tc)
deriving instance Data (ImportDecl Zk)

deriving instance Data (IE Ps)
deriving instance Data (IE Rn)
deriving instance Data (IE Tc)
deriving instance Data (IE Zk)

deriving instance Eq (IE Ps)
deriving instance Eq (IE Rn)
deriving instance Eq (IE Tc)
deriving instance Eq (IE Zk)

deriving instance Data CsThingRn

deriving instance Data XXExprTc
deriving instance Data XXExprZk
deriving instance Data XXPatCsTc
