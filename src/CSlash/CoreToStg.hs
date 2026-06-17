{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.CoreToStg (CoreToStgOpts(..), coreToStg) where

import CSlash.Core
import CSlash.Core.Make
import CSlash.Core.Utils
import CSlash.Core.Opt.Arity ( manifestArity )
import CSlash.Core.Type
import CSlash.Core.TyCon
import CSlash.Core.DataCon

import CSlash.Stg.Syntax
-- import CSlash.Stg.Debug
import CSlash.Stg.Make
-- import CSlash.Stg.Utils (allowTopLevelConApp)

import CSlash.Types.RepType
--import GHC.Types.Id.Make ( coercionTokenId )
import CSlash.Types.Var
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
-- import CSlash.Types.CostCentre
import CSlash.Types.Tickish
import CSlash.Types.Var.Env
import CSlash.Types.Name ( isExternalName )
import CSlash.Types.Basic ( Arity, TypeOrConstraint(..) )
import CSlash.Types.Literal
-- import GHC.Types.ForeignCall
-- import GHC.Types.IPE

import CSlash.Unit.Module
import CSlash.Platform ( Platform )
import CSlash.Platform.Ways
-- import CSlash.Builtin.PrimOps

import CSlash.Utils.Outputable
import CSlash.Utils.Monad
import CSlash.Utils.Misc (HasDebugCallStack)
import CSlash.Utils.Panic
import CSlash.Utils.Trace

import Control.Monad (ap)
import Data.Maybe (mapMaybe)

coreToStg
  :: CoreToStgOpts
  -> Module
  -> ModLocation
  -> CoreProgram
  -> [StgTopBinding]
coreToStg opts this_mod ml pgm
  = pgm''
  where
    (_, pgm') = coreTopBindsToStg opts this_mod emptyVarEnv pgm

    !pgm'' = pgm'

coreTopBindsToStg
  :: CoreToStgOpts
  -> Module
  -> VarEnv CoreId HowBound
  -> CoreProgram
  -> (VarEnv CoreId HowBound, [StgTopBinding])
coreTopBindsToStg _ _ env [] = (env, [])
coreTopBindsToStg opts this_mod env (b:bs)
  = (env2, b' : bs')
  where
    (env1, b') = coreTopBindToStg opts this_mod env b
    (env2, bs') = coreTopBindsToStg opts this_mod env1 bs

coreTopBindToStg
  :: CoreToStgOpts
  -> Module
  -> VarEnv CoreId HowBound
  -> CoreBind
  -> (VarEnv CoreId HowBound, StgTopBinding)
coreTopBindToStg _ _ env (NonRec id e)
  | Just str <- exprIsTickedString_maybe e
  = let env' = extendVarEnv env id how_bound
        how_bound = LetBound TopLet 0
    in (env', StgTopStringLit id str)
    
coreTopBindToStg opts@CoreToStgOpts{ coreToStg_platform = platform } this_mod env (NonRec id rhs)
  = let env' = extendVarEnv env id how_bound
        how_bound = LetBound TopLet $! manifestArity rhs

        (id', stg_rhs) = initCts platform env $ coreToTopStgRhs opts this_mod (id, rhs)

        bind = StgTopBind $ StgNonRec id' stg_rhs
    in (env', bind)

coreTopBindToStg opts@CoreToStgOpts{ coreToStg_platform = platform } this_mod env (Rec pairs)
  = assert (not (null pairs)) $
    let extra_env' = [ (b, LetBound TopLet $! manifestArity rhs)
                     | (b, rhs) <- pairs ]
        env' = extendVarEnvList env extra_env'

        stg_rhss = initCts platform env' $ mapM (coreToTopStgRhs opts this_mod) pairs
        bind = StgTopBind $ StgRec stg_rhss
    in (env', bind)

coreToTopStgRhs
  :: CoreToStgOpts
  -> Module
  -> (CoreId, CoreExpr)
  -> CtsM (CoreId, StgRhs)
coreToTopStgRhs opts this_mod (bndr, rhs) = do
  new_rhs <- coreToMkStgRhs bndr rhs
  let stg_rhs = mkTopStgRhs (panic "allowTopLevelConApp (coreToStg_platform opts)"
                             (coreToStg_ExternalDynamicRefs opts))
                this_mod bndr new_rhs
      stg_arity = stgRhsArity stg_rhs
  pure (bndr, assertPpr (arity_ok stg_arity) (mk_arity_msg stg_arity) stg_rhs)
  where
    arity_ok stg_arity
      | isExternalName (varName bndr) = id_arity == stg_arity
      | otherwise = True

    id_arity = idArity bndr
    mk_arity_msg stg_arity = vcat [ ppr bndr
                                  , text "Id arity:" <+> ppr id_arity
                                  , text "STG arity:" <+> ppr stg_arity ]

-- ---------------------------------------------------------------------------
-- Expressions
-- ---------------------------------------------------------------------------

coreToStgExpr :: HasDebugCallStack => CoreExpr -> CtsM StgExpr
coreToStgExpr (Lit _) = panic "coreToStgExpr Lit"
coreToStgExpr (Var v) = coreToStgApp v [] []
coreToStgExpr expr@App{}
  = case app_head of
      Var f -> coreToStgApp f args ticks
      Lit l -> panic "isLitRubbish"
      _ -> pprPanic "coreToStgExpr - Invalid app head:" (ppr expr)
  where
    (app_head, args, ticks) = myCollectArgs expr
coreToStgExpr expr@Lam{}
  = let (args, body) = myCollectBinders expr
    in case filterStgBinders args of
         [] -> coreToStgExpr body
         _ -> pprPanic "coreToStgExpr" $ text "Unexpected value lambda:" $$ ppr expr
coreToStgExpr (Tick tick expr) = panic "coreToStgExpr Tick"
coreToStgExpr (Cast expr _) = coreToStgExpr expr
coreToStgExpr (Case scrut bndr _ alts)
  | null alts
  = panic "coreToStgExpr empty case"
  | otherwise
  = do scrut2 <- coreToStgExpr scrut
       alts2 <- extendVarEnvCts [(bndr, LambdaBound)] (mapM vars_alt alts)
       return (StgCase scrut2 bndr (mkStgAltType bndr alts) alts2)
  where
    vars_alt :: CoreAlt -> CtsM StgAlt
    vars_alt (Alt con binders rhs)
      = extendVarEnvCts [(b, LambdaBound) | b <- binders] $ do
          rhs2 <- coreToStgExpr rhs
          return $! GenStgAlt { alt_con = con
                              , alt_bndrs = binders
                              , alt_rhs = rhs2 }
coreToStgExpr (Let bind body) = coreToStgLet bind body
coreToStgExpr e = pprPanic "coreToStgExpr" (ppr e)

mkStgAltType :: CoreId -> [CoreAlt] -> AltType
mkStgAltType bndr alts
  -- | isTupleType bndr_ty || isSumType bndr_ty
  -- = panic "mkStgAltType"
  -- | otherwise
  = panic "mkStgAltType"

-- ---------------------------------------------------------------------------
-- Applications
-- ---------------------------------------------------------------------------
coreToStgApp :: CoreId -> [CoreArg] -> [CoreTickish] -> CtsM StgExpr
coreToStgApp f args ticks = do
  (args', ticks') <- coreToStgArgs args
  how_bound <- lookupVarCts f

  let n_val_args = valArgCount args
      f_arity = stgArity f how_bound
      saturated = f_arity <= n_val_args

      res_ty = exprType (mkCoreApps (Var f) args)
      app = case idDetails f of
              DataConId dc
                | saturated -> if isSumDataCon dc
                               then StgConApp dc NoNumber args' (sumPrimReps args)
                               else StgConApp dc NoNumber args' []

              -- PrimOpId TODO

              -- FCallId TODO

              TickBoxOpId{} -> pprPanic "coreToStg TickBox" $ ppr (f, args')

              _ -> StgApp f args'

      add_tick !t !e = StgTick t e
      tapp = foldr add_tick app (map (coreToStgTick res_ty) ticks ++ ticks')

  app `seq` return tapp

sumPrimReps :: [CoreArg] -> [[PrimRep]]
sumPrimReps args
  = let val_args = dropWhile isNonValArg args
    in typePrimRep . exprType <$> val_args

-- ---------------------------------------------------------------------------
-- Argument lists
-- ---------------------------------------------------------------------------

getStgArgFromTrivialArg :: HasDebugCallStack => CoreArg -> StgArg
getStgArgFromTrivialArg e = trivial_expr_fold StgVarArg StgLitArg panic panic e
  where panic = pprPanic "getStgArgFromTrivialArg" (ppr e)

coreToStgArgs :: [CoreArg] -> CtsM ([StgArg], [StgTickish])
coreToStgArgs [] = return ([], [])
coreToStgArgs (Type _ : args) = coreToStgArgs args
coreToStgArgs (KiCo _ : args) = coreToStgArgs args
coreToStgArgs (Kind _ : args) = coreToStgArgs args
coreToStgArgs (arg : args) = do
  (stg_args, ticks) <- coreToStgArgs args

  platform <- getPlatform
  let arg_ty = exprType arg
      ticks' = map (coreToStgTick arg_ty) (stripTicksT (not . tickishIsCode) arg)
      arg' = getStgArgFromTrivialArg arg
      -- arg_rep = 
      -- stg_arg+rep = 
      bad_args = not (panic "bad_args")

  massertPpr (length ticks' <= 1) (text "More than one Tick in trivial arg:" <+> ppr arg)
  warnPprTraceM bad_args "Dangerous-looking argument. Shouldn't happen" (ppr arg)

  return (arg' : stg_args, ticks' ++ ticks)

coreToStgTick :: CoreType -> CoreTickish -> StgTickish
coreToStgTick _ (CpcTick m i) = CpcTick m i

-- ---------------------------------------------------------------------------
-- The magic for lets:
-- ---------------------------------------------------------------------------

coreToStgLet :: CoreBind -> CoreExpr -> CtsM StgExpr
coreToStgLet bind body = do
  (bind2, env_ext) <- vars_bind bind

  body2 <- extendVarEnvCts env_ext $ coreToStgExpr body

  let new_let | isJoinBind bind
              = StgLetNoEscape noExtFieldSilent bind2 body2
              | otherwise
              = StgLet noExtFieldSilent bind2 body2
  return new_let
  where
    mk_binding binder rhs
      = (binder, LetBound NestedLet (manifestArity rhs))

    vars_bind :: CoreBind -> CtsM (StgBinding, [(CoreId, HowBound)])
    vars_bind (NonRec binder rhs) = do
      rhs2 <- coreToStgRhs (binder, rhs)
      let env_ext_item = mk_binding binder rhs
      return (StgNonRec binder rhs2, [env_ext_item])
    vars_bind (Rec pairs)
      = let binders = map fst pairs
            env_ext = [ mk_binding b rhs | (b, rhs) <- pairs ]
        in extendVarEnvCts env_ext $ do
             rhss2 <- mapM coreToStgRhs pairs
             return (StgRec (binders `zip` rhss2), env_ext)

coreToStgRhs :: (CoreId, CoreExpr) -> CtsM StgRhs
coreToStgRhs (bndr, rhs) = do
  new_rhs <- coreToMkStgRhs bndr rhs
  return (mkStgRhs bndr new_rhs)

coreToMkStgRhs :: HasDebugCallStack => CoreId -> CoreExpr -> CtsM MkStgRhs
coreToMkStgRhs bndr expr = do
  let (args, body) = myCollectBinders expr
      args' = filterStgBinders args
  extendVarEnvCts [ (a, LambdaBound) | a <- args' ] $ do
    body' <- coreToStgExpr body
    pure MkStgRhs { rhs_args = args'
                  , rhs_expr = body'
                  , rhs_type = exprType body
                  , rhs_is_join = isJoinId bndr }

-- ---------------------------------------------------------------------------
-- A monad for the core-to-STG pass
-- ---------------------------------------------------------------------------

newtype CtsM a = CtsM { unCtsM :: Platform -> VarEnv CoreId HowBound -> a }
  deriving Functor

data HowBound
  = ImportBound
  | LetBound LetInfo Arity
  | LambdaBound
  deriving Eq

data LetInfo
  = TopLet
  | NestedLet
  deriving Eq

initCts :: Platform -> VarEnv CoreId HowBound -> CtsM a -> a
initCts platform env m = unCtsM m platform env

returnCts :: a -> CtsM a
returnCts e = CtsM $ \_ _ -> e
{-# INLINE returnCts #-}

thenCts :: CtsM a -> (a -> CtsM b) -> CtsM b
thenCts m k = CtsM $ \platform env -> unCtsM (k (unCtsM m platform env)) platform env
{-# INLINE thenCts #-}

instance Applicative CtsM where
  pure = returnCts
  (<*>) = ap

instance Monad CtsM where
  (>>=) = thenCts

getPlatform :: CtsM Platform
getPlatform = CtsM const

extendVarEnvCts :: [(CoreId, HowBound)] -> CtsM a -> CtsM a
extendVarEnvCts ids_w_howbound expr
  = CtsM $ \platform env -> unCtsM expr platform (extendVarEnvList env ids_w_howbound)

lookupVarCts :: CoreId -> CtsM HowBound
lookupVarCts v = CtsM $ \_ env -> lookupBinding env v

lookupBinding :: VarEnv CoreId HowBound -> CoreId -> HowBound
lookupBinding env v = case lookupVarEnv env v of
  Just x -> x
  Nothing -> assertPpr (isGlobalId v) (ppr v) ImportBound

filterStgBinders :: [CoreBndr] -> [CoreId]
filterStgBinders = mapMaybe runtimeVar_maybe

myCollectBinders :: CoreExpr -> ([CoreBndr], CoreExpr)
myCollectBinders expr
  = go [] expr
  where
    go bs (Lam b _ e) = go (b : bs) e
    go bs (Cast e _) = go bs e
    go bs e = (reverse bs, e)

myCollectArgs :: HasDebugCallStack => CoreExpr -> (CoreExpr, [CoreArg], [CoreTickish])
myCollectArgs expr
  = go expr [] []
  where
    go h@Var{} as ts = (h, as, ts)
    go (App f a) as ts = go f (a:as) ts
    go (Tick t e) as ts = assertPpr (not (tickishIsCode t) || all isNonValArg as)
                          (ppr e $$ ppr as $$ ppr ts) $
                          go e as (t:ts)
    go (Cast e _) as ts = go e as ts
    go (Case e b _ alts) as ts
      | null alts
      = panic "emptyCase"
    go (Lam b _ e) as ts
      | isNonRuntimeVar b = go e (drop 1 as) ts
    go e as ts = (e, as, ts)

stgArity :: CoreId -> HowBound -> Arity
stgArity _ (LetBound _ arity) = arity
stgArity f ImportBound = idArity f
stgArity _ LambdaBound = 0

data CoreToStgOpts = CoreToStgOpts
  { coreToStg_platform :: Platform
  , coreToStg_ways :: Ways
  , coreToStg_ExternalDynamicRefs :: Bool
  }
