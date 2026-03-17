module CSlash.CsToCore.Match.Literal where

import CSlash.Platform

-- import {-# SOURCE #-} GHC.HsToCore.Match ( match )
-- import {-# SOURCE #-} GHC.HsToCore.Expr  ( dsExpr, dsSyntaxExpr )

import CSlash.CsToCore.Errors.Types
import CSlash.CsToCore.Monad
import CSlash.CsToCore.Utils

import CSlash.Cs

-- import GHC.Tc.Utils.TcMType ( shortCutLit )
import CSlash.Tc.Utils.TcType

import CSlash.Core
import CSlash.Core.Make
import CSlash.Core.TyCon
import CSlash.Core.Reduction ( TyReduction(..) )
import CSlash.Core.DataCon
import CSlash.Core.Type

import CSlash.Types.Name
import CSlash.Types.Literal
import CSlash.Types.SrcLoc

import CSlash.Builtin.Names
import CSlash.Builtin.Types
import CSlash.Builtin.Types.Prim

import CSlash.Types.Var.Id
import CSlash.Types.SourceText

import CSlash.Driver.DynFlags

import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic
-- import CSlash.Utils.Unique (sameUnique)

import CSlash.Data.FastString
--- import qualified CSlash.Data.List.NonEmpty as NEL

import Control.Monad
import Data.Int
import Data.List.NonEmpty (NonEmpty(..))
import Data.Word
import GHC.Real ( Ratio(..), numerator, denominator )

{- *********************************************************************
*                                                                      *
                 Warnings about overflowed literals
*                                                                      *
********************************************************************* -}

warnAboutOverflowedOverLit :: CsOverLit Zk -> DsM ()
warnAboutOverflowedOverLit csOverLit = do
  dflags <- getDynFlags
  panic "warnAboutOverflowerdLiterals dflags $ getIntegralLit csOverLit"

warnAboutOverflowedLit :: CsLit Zk -> DsM ()
warnAboutOverflowedLit csLit = do
  dflags <- getDynFlags
  panic "warnAboutOverflowedLiterals"

{- *********************************************************************
*                                                                      *
                Tidying lit pats
*                                                                      *
********************************************************************* -}

tidyLitPat :: CsLit Zk -> Pat Zk
tidyLitPat = panic "tidyLitPat"

{- *********************************************************************
*                                                                      *
                Pattern matching on LitPat
*                                                                      *
********************************************************************* -}

matchLiterals
  :: NonEmpty (Id Zk)
  -> Type Zk
  -> NonEmpty (NonEmpty EquationInfoNE)
  -> DsM (MatchResult CoreExpr)
matchLiterals (var :| vars) ty sub_groups = panic "matchLiterals"

{- *********************************************************************
*                                                                      *
                Pattern matching on NPat
*                                                                      *
********************************************************************** -}

matchNPats :: NonEmpty (Id Zk) -> Type Zk -> NonEmpty EquationInfoNE -> DsM (MatchResult CoreExpr)
matchNPats (var :| vars) ty (eqn1 :| eqns) = panic "matchNPats"
