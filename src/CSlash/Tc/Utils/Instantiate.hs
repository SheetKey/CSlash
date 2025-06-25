module CSlash.Tc.Utils.Instantiate where

import CSlash.Driver.Session
import CSlash.Driver.Env

-- import GHC.Builtin.Types  ( heqDataCon, integerTyConName )
import CSlash.Builtin.Names

import CSlash.Cs
-- import GHC.Hs.Syn.Type   ( hsLitType )

-- import GHC.Core.InstEnv
-- import GHC.Core.FamInstEnv
import CSlash.Core.Predicate
import CSlash.Core ( Expr(..) ) 
import CSlash.Core.Type
import CSlash.Core.Type.Subst
import CSlash.Core.Kind
import CSlash.Core.Kind.Subst
-- import CSlash.Core.TyCo.Ppr ( debugPprType )
-- import GHC.Core.Class( Class )
import CSlash.Core.DataCon
-- import GHC.Core.Coercion.Axiom

-- import {-# SOURCE #-}   GHC.Tc.Gen.Expr( tcCheckPolyExpr, tcSyntaxOp )
import {-{-# SOURCE #-}-} CSlash.Tc.Utils.Unify( unifyKind )
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Origin
import CSlash.Tc.Utils.Env
import CSlash.Tc.Types.Evidence
-- import GHC.Tc.Instance.FunDeps
-- import GHC.Tc.Utils.Concrete ( hasFixedRuntimeRep_syntactic )
import CSlash.Tc.Utils.TcMType
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Errors.Types
import CSlash.Tc.Zonk.Monad ( ZonkM )

-- import GHC.Types.Id.Make( mkDictFunId )
import CSlash.Types.Basic ( TypeOrKind(..), Arity )
import CSlash.Types.Error
import CSlash.Types.SourceText
import CSlash.Types.SrcLoc as SrcLoc
import CSlash.Types.Var.Env
import CSlash.Types.Id
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Var

import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Outputable
-- import CSlash.Utils.Unique (sameUnique)

import CSlash.Unit.State
import CSlash.Unit.External
import CSlash.Unit.Module.Warnings

import Data.List ( mapAccumL )
import qualified Data.List.NonEmpty as NE
import Control.Monad( when, unless )
import Data.Function ( on )

{- *********************************************************************
*                                                                      *
            Instantiating a call
*                                                                      *
********************************************************************* -}

instCallKiConstraints :: CtOrigin -> [AnyPredKind] -> TcM [KiEvType]
instCallKiConstraints orig preds
  | null preds
  = return []
  | otherwise
  = do evs <- mapM go preds
       traceTc "instCallKiConstraints" (ppr evs)
       return evs
  where
    go :: AnyPredKind -> TcM KiEvType
    go pred
      | KiConApp EQKi [k1, k2] <- pred
      = do co <- unifyKind Nothing k1 k2
           return $ kiEvCoercion co
      | otherwise
      = emitWanted orig pred

{- *********************************************************************
*                                                                      *
         Instantiating Kinds
*                                                                      *
********************************************************************* -}

tcInstInvisibleKiBinder :: KvSubst AnyKiVar -> AnyKiVar -> TcM (KvSubst AnyKiVar, AnyType)
tcInstInvisibleKiBinder subst kv = do
  (subst', kv') <- newMetaKiVarX subst kv
  return (subst', Embed $ mkKiVarKi kv')
