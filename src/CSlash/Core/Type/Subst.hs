module CSlash.Core.Type.Subst where

import {-# SOURCE #-} CSlash.Core.Type
   ( mkCastTy, mkAppTy, isCoercionTy, mkTyConApp, getTyVar_maybe )
import {-# SOURCE #-} CSlash.Core.Type.Ppr ( pprTyVar )

import CSlash.Core.Type.Rep

import CSlash.Types.Var
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env

import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.Misc
import CSlash.Types.Unique
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.Set
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

{- **********************************************************************
*                                                                       *
                        Substitutions
*                                                                       *
********************************************************************** -}

data Subst = Subst InScopeSet IdSubstEnv TvSubstEnv

type IdSubstEnv = IdEnv CoreExpr

type TvSubstEnv = TyVarEnv Type

emptySubst :: Subst
emptySubst = Sybst emptyInScopeSet emptyVarEnv emptyVarEnv emptyVarEnv
