{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module CSlash.Language.Syntax.Extension where

import Data.Kind (Type)
import Data.Data

data NoExtField = NoExtField
  deriving (Data, Eq, Ord)

noExtField :: NoExtField
noExtField = NoExtField

data DataConCantHappen
  deriving (Data, Eq, Ord)

dataConCantHappen :: DataConCantHappen -> a
dataConCantHappen x = case x of {}

type family XRec p a = r | r -> a

type family Anno a = b

class UnXRec p where
  unXRec :: XRec p a -> a

class MapXRec p where
  mapXRec :: (Anno a ~ Anno b) => (a -> b) -> XRec p a -> XRec p b

class WrapXRec p a where
  wrapXRec :: a -> XRec p a

type family IdP p

type LIdP p = XRec p (IdP p)

-- =====================================================================
-- Type families for the CsBinds extension points

-- CsLocalBindsLR type families
type family XCsValBinds x x'
type family XEmptyLocalBinds x x'

-- CsValBindsLR type families
type family XValBinds x x'
type family XXValBindsLR x x'

-- CsBindLR type families
type family XFunBind x x'
type family XTyFunBind x x'
type family XTCVarBind x x'
type family XXCsBindsLR x x'

-- Sig type families
type family XTypeSig x
type family XKindSig x
type family XFixSig x

-- FixitySig type families
type family XFixitySig x

-- =====================================================================
-- Type families for the CsDecls extension points

-- CsDecl type families
type family XValD x
type family XSigD x

-- -------------------------------------
-- HsGroup type families
type family XCCsGroup x

-- -------------------------------------
-- TyClGroup type families
type family XCTypeGroup x

-- =====================================================================
-- Type families for the HsModule extension points

type family XCModule x

-- =====================================================================
-- Type families for the CsExpr extension points

type family XVar x
type family XUnboundVar x
type family XOverLitE x
type family XLitE x
type family XLam x
type family XApp x
type family XTyLam x
type family XTyApp x
type family XOpApp x
type family XNegApp x
type family XPar x
type family XSectionL x
type family XSectionR x
type family XExplicitTuple x
type family XExplicitSum x
type family XCase x
type family XIf x
type family XMultiIf x
type family XLet x
type family XExprWithTySig x
type family XEmbTy x

-- -------------------------------------
-- HsTupArg type families
type family XPresent  x
type family XMissing  x

-- -------------------------------------
-- MatchGroup type families
type family XMG x b

-- -------------------------------------
-- Match type families
type family XCMatch x b

-- -------------------------------------
-- GRHSs type families
type family XCGRHSs x b

-- -------------------------------------
-- GRHS type families
type family XCGRHS x b

-- -------------------------------------
-- StmtLR type families
type family XBindStmt x x' b
type family XBodyStmt x x' b
type family XLetStmt x x' b

-- =====================================================================
-- Type families for the CsLit extension points

type family XCsChar x
type family XCsString x
type family XCsInt x
type family XCsDouble x
type family XSigPat x
type family XKdSigPat x
type family XImpPat x

-- -------------------------------------
-- CsOverLit type families
type family XOverLit  x

-- =====================================================================
-- Type families for the CsPat extension points

type family XWildPat x
type family XAsPat x
type family XParPat x
type family XVarPat x
type family XTyVarPat x
type family XTuplePat x
type family XSumPat x
type family XConPat x
type family XLitPat x
type family XNPat x
type family XXPat x

-- =====================================================================
-- Type families for the CsTypes type families

-- -------------------------------------
-- CsSigType type families
type family XCsSig x

-- -------------------------------------
-- HsPatSigType type families
type family XCsPS x

-- -------------------------------------
-- CsTyPat type families
type family XCsTP x

-- -------------------------------------
-- CsType type families
type family XForAllTy x
type family XQualTy x
type family XTyVar x
type family XUnboundTyVar x
type family XAppTy x
type family XFunTy x
type family XTupleTy x
type family XSumTy x
type family XOpTy x
type family XParTy x
type family XKdSig x
type family XTyLamTy x
type family XTyAppTy x
type family XTySectionL x
type family XTySectionR x

-- -------------------------------------
-- HsTupArg type families
type family XTyPresent  x
type family XTyMissing  x

-- ---------------------------------------------------------------------
-- CsForAllTelescope type families
type family XCsForAll x

-- ---------------------------------------------------------------------
-- CsTyVarBndr type families
-- type family XUserTyVar   x
type family XKindedTyVar x
type family XImpKindedTyVar x

-- =====================================================================
-- Type families for the CsImpExp type families

-- -------------------------------------
-- ImportDecl type families
type family XCImportDecl       x

-- -------------------------------------
-- IE type families
type family XIEVar x
type family XIEModuleContents x
type family XIETyVar x

-- -------------------------------------
-- IEWrappedName type families
type family XIEName p
type family XIETyName p

-- =====================================================================
-- Type families for the CsKind type families
type family XUKd x
type family XAKd x
type family XLKd x
type family XKdVar x
type family XFunKd x
type family XQualKd x
type family XParKd x

type family XKdLT x
type family XKdLTEQ x

-- -------------------------------------
-- CsPatSigKind type families
type family XCsPSK x

-- =====================================================================
-- Misc

type family NoTc (p :: Type)
