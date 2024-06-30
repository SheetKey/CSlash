{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module CSlash.Language.Syntax.Extension where

import Data.Kind (Type)

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

-- CsValBindsLR type families
type family XValBinds x x'

-- CsBindLR type families
type family XFunBind x x'
type family XTySynBind x x'
type family XVarBind x x'

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

-- =====================================================================
-- Type families for the CsExpr extension points

type family XVar x
type family XUnboundVar x
type family XLitE x
type family XLam x
type family XApp x
type family XTyLam x
type family XTyApp x
type family XOpApp x
type family XPar x
type family XSectionL x
type family XSectionR x
type family XExplicitTuple x
type family XExplicitSum x
type family XCase x
type family XIf x
type family XMultiIf x
type family XExprWithTySig x

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
type family XGuardBodyStmt x x' b

-- =====================================================================
-- Type families for the CsLit extension points

type family XCsChar x
type family XCsString x
type family XCsInt x
type family XCsDouble x
type family XSigPat x

-- -------------------------------------
-- CsOverLit type families
type family XOverLit  x

-- =====================================================================
-- Type families for the CsPat extension points

type family XWildPat x
type family XVarPat x
type family XTuplePat x
type family XSumPat x
type family XLitPat x

-- =====================================================================
-- Type families for the CsTypes type families

-- -------------------------------------
-- HsSigType type families
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
type family XTyVar x
type family XAppTy x
type family XFunTy x
type family XTupleTy x
type family XSumTy x
type family XParTy x
type family XKdSig x

-- ---------------------------------------------------------------------
-- CsForAllTelescope type families
type family XCsForAllInvis x

-- ---------------------------------------------------------------------
-- CsTyVarBndr type families
-- type family XUserTyVar   x
type family XKindedTyVar x

-- =====================================================================
-- Type families for the CsImpExp type families

-- -------------------------------------
-- ImportDecl type families
type family XCImportDecl       x

-- -------------------------------------
-- IE type families
type family XIEVar x
type family XIEModuleContents x

-- -------------------------------------
-- IEWrappedName type families
type family XIEName p

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

-- =====================================================================
-- Misc

type family NoTc (p :: Type)
