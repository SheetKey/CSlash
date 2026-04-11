{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Opt.Simplify.Iteration where

import CSlash.Driver.Flags

import CSlash.Core
import CSlash.Core.Opt.Simplify.Monad
-- import GHC.Core.Opt.ConstantFold
import CSlash.Core.Type
import CSlash.Core.Type.Compare( eqType )
import CSlash.Core.Kind
import CSlash.Core.Opt.Simplify.Env
-- import CSlash.Core.Opt.Simplify.Inline
import CSlash.Core.Opt.Simplify.Utils
import CSlash.Core.Opt.OccurAnal
  ( occurAnalyzeExpr{-, zapLambdaBndrs, scrutOkForBinderSwap, BinderSwapDecision (..)-} )
import CSlash.Core.Make ( FloatBind{-, mkImpossibleExpr, castBottomExpr-} )
import qualified CSlash.Core.Make as Make
import CSlash.Core.Reduction
import CSlash.Core.Opt.Coercion ( optKiCoercion )
import CSlash.Core.DataCon
   ( DataCon, dataConId
--   , dataConRepArgTys, isUnboxedTupleDataCon
   )
-- import CSlash.Core.Opt.Stats ( Tick(..) )
import CSlash.Core.Ppr ( pprCoreExpr )
import CSlash.Core.Unfold
import CSlash.Core.Unfold.Make
import CSlash.Core.Utils
import CSlash.Core.Opt.Arity ( ArityType{-, exprArity-}, arityTypeBotSigs_maybe
                             {-, pushCoTyArg, pushCoValArg, exprIsDeadEnd-}
                             , typeArity{-, arityTypeArity, etaExpandAT-} )
import CSlash.Core.SimpleOpt
  ( exprIsConApp_maybe, joinPointBinding_maybe, joinPointBindings_maybe )

-- import GHC.Types.Literal   ( litIsLifted ) --, mkLitInt ) -- temporarily commented out. See #8326
import CSlash.Types.SourceText
import CSlash.Types.Var.Id
-- import CSlash.Types.Id.Make   ( seqId )
import CSlash.Types.Var.Id.Info
import CSlash.Types.Name ( mkSystemVarName, isExternalName, getOccFS )
import CSlash.Types.Demand
import CSlash.Types.Unique ( hasKey )
import CSlash.Types.Basic
import CSlash.Types.Tickish
-- import GHC.Builtin.Types.Prim( realWorldStatePrimTy )
-- import GHC.Builtin.Names( runRWKey, seqHashKey )

import CSlash.Data.Maybe ( isNothing, orElse, mapMaybe )
import CSlash.Data.FastString
import CSlash.Unit.Module ( moduleName )
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.Monad  ( mapAccumLM, liftIO )
import CSlash.Utils.Logger
import CSlash.Utils.Misc

import Control.Monad

{- *********************************************************************
*                                                                      *
        Bindings
*                                                                      *
********************************************************************* -}

simplTopBinds :: SimplEnv -> [InBind] -> SimplM (SimplFloats, SimplEnv)
simplTopBinds env0 binds0 = do
  !env1 <- {-# SCC "simplTopBinds-simplRecBndrs" #-} simplRecBndrs env0 (bindersOfBinds binds0)

  (floats, env2) <- {-# SCC "simplTopBinds-simpl_binds" #-} simpl_binds env1 binds0
  freeTick SimplifierDone
  return (floats, env2)
  where
    simpl_binds :: SimplEnv -> [InBind] -> SimplM (SimplFloats, SimplEnv)
    simpl_binds env [] = return (emptyFloats env, env)
    simpl_binds env (bind:binds) = do
      (float, env1) <- simpl_bind env bind
      (floats, env2) <- simpl_binds env1 binds
      let !floats1 = float `addFloats` floats
      return (floats1, env2)

    simpl_bind env (Rec pairs) = simplRecBind env (BC_Let TopLevel Recursive) pairs
    simpl_bind env (NonRec b r) = do
      let bind_cxt = BC_Let TopLevel NonRecursive
      -- (env', b') <- 

      panic "unfinished"
