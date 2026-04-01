{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module CSlash.Core.Opt.SetLevels where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Core as Core
import CSlash.Core.Opt.Monad ( FloatOutSwitches(..) )
import CSlash.Core.Utils
import CSlash.Core.Opt.Arity   ( exprBotStrictness_maybe, isOneShotBndr )
import CSlash.Core.FVs     -- all of it
import CSlash.Core.Subst
import CSlash.Core.Make
import CSlash.Core.Type    ( Type, varsOfType
                           --, closeOverKindsDSet
                           )
import CSlash.Core.Kind

import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.Var
import CSlash.Types.Var.Set
import CSlash.Types.Unique.Set   ( nonDetStrictFoldUniqSet )
import CSlash.Types.Unique.DSet  ( getUniqDSet )
import CSlash.Types.Var.Env
import CSlash.Types.Literal      ( litIsTrivial )
import CSlash.Types.Demand       ( DmdSig, prependArgsDmdSig )
-- import CSlash.Types.Cpr          ( CprSig, prependArgsCprSig )
import CSlash.Types.Name         ( getOccName, mkSystemVarName )
import CSlash.Types.Name.Occurrence ( occNameFS )
import CSlash.Types.Unique       ( Uniquable, hasKey )
import CSlash.Types.Tickish      ( tickishIsCode )
import CSlash.Types.Unique.Supply
import CSlash.Types.Unique.DFM
import CSlash.Types.Basic  ( Arity, RecFlag(..), isRec )

import CSlash.Builtin.Types
-- import CSlash.Builtin.Names      ( runRWKey )

import CSlash.Data.FastString

import CSlash.Utils.FV
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Trace

import Data.Maybe

{- *********************************************************************
*                                                                      *
                  Level numbers
*                                                                      *
********************************************************************* -}

type LevelledExpr = TaggedExpr FloatSpec
type LevelledBind = TaggedBind FloatSpec
type LevelledLetBndr = TaggedLetBndr FloatSpec
type LevelledLamBndr = TaggedLamBndr FloatSpec

data Level = Level Int Int

data FloatSpec
  = FloatMe Level
  | StayPut Level

floatSpecLevel :: FloatSpec -> Level
floatSpecLevel (FloatMe l) = l
floatSpecLevel (StayPut l) = l

instance Outputable FloatSpec where
  ppr (FloatMe l) = char 'F' <> ppr l
  ppr (StayPut l) = ppr l

tOP_LEVEL :: Level
tOP_LEVEL = Level 0 0

incMajorLvl :: Level -> Level
incMajorLvl (Level major _) = Level (major + 1) 0

incMinorLvl :: Level -> Level
incMinorLvl (Level major minor) = Level major (minor + 1)

maxLvl :: Level -> Level -> Level
maxLvl l1@(Level maj1 min1) l2@(Level maj2 min2)
  | (maj1 > maj2) || (maj1 == maj2 && min1 > min2) = l1
  | otherwise = l2

ltLvl :: Level -> Level -> Bool
ltLvl (Level maj1 min1) (Level maj2 min2)
  = (maj1 < maj2) || (maj1 == maj2 && min1 < min2)

ltMajLvl :: Level -> Level -> Bool
ltMajLvl (Level maj1 _) (Level maj2 _) = maj1 < maj2

isTopLvl :: Level -> Bool
isTopLvl (Level 0 0) = True
isTopLvl _ = False

instance Outputable Level where
  ppr (Level maj min) = hcat [ char '<', int maj, char ',', int min, char '>' ]

instance Eq Level where
  (Level maj1 min1) == (Level maj2 min2) = maj1 == maj2 && min1 == min2

{- *********************************************************************
*                                                                      *
                  Main level-setting code
*                                                                      *
********************************************************************* -}

setLevels
  :: FloatOutSwitches
  -> CoreProgram
  -> UniqSupply
  -> [LevelledBind]
setLevels float_lams binds us = initLvl us (do_them binds)
  where
    env = initialEnv float_lams binds

    do_them :: [CoreBind] -> LvlM [LevelledBind]
    do_them [] = return []
    do_them (b:bs) = do
      lvld_bind <- lvlTopBind env b
      lvld_binds <- do_them bs
      return (lvld_bind : lvld_binds)

lvlTopBind :: LevelEnv -> CoreBind -> LvlM LevelledBind
lvlTopBind env (NonRec bndr rhs) = do
  (bndr', rhs') <- lvl_top env NonRecursive bndr rhs
  return (NonRec bndr' rhs')
lvlTopBind env (Rec pairs) = do
  prs' <- mapM (\(b, r) -> lvl_top env Recursive b r) pairs
  return (Rec prs')

lvl_top :: LevelEnv -> RecFlag -> CoreId -> CoreExpr -> LvlM (LevelledLetBndr, LevelledExpr)
lvl_top env is_rec bndr rhs = do
  rhs' <- lvlRhs env is_rec (isDeadEndId bndr) NotJoinPoint (freeVars rhs)
  return (stayPutLet tOP_LEVEL bndr, rhs')

{- *********************************************************************
*                                                                      *
                  Setting expression levels
*                                                                      *
********************************************************************* -}

lvlExpr
  :: LevelEnv
  -> CoreExprWithFVs
  -> LvlM LevelledExpr
lvlExpr env (_, AnnType ty) = return (Type (substTyUnchecked (le_subst env) ty))
lvlExpr env (_, AnnKiCo co) = return (KiCo (substKiCo (le_subst env) co))
lvlExpr env (_, AnnKind ki) = return (Kind (substMonoKi (le_subst env) ki))
lvlExpr env (_, AnnVar v) = return (lookupVar env v)
lvlExpr _ (_, AnnLit lit) = return (Lit lit)
lvlExpr env (_, AnnCast expr (_, co)) = do
  expr' <- lvlNonTailExpr env expr
  return (Cast expr' (panic "substTyCo (le_subst env) co"))
lvlExpr env (_, AnnTick tickish expr) = do
  expr' <- lvlNonTailExpr env expr
  let tickish' = substTickish (le_subst env) tickish
  return (Tick tickish' expr')
lvlExpr env expr@(_, AnnApp _ _) = lvlApp env expr (collectAnnArgs expr)
lvlExpr env expr@(_, AnnLam {}) = do
  new_body <- lvlNonTailMFE new_env True body
  return (mkCoreLams new_bndrs new_body)
  where
    (bndrs, body) = collectAnnBndrs expr
    (env1, bndrs1) = substLamBndrsSL env bndrs
    (new_env, new_bndrs) = lvlLamBndrs env1 (le_ctxt_lvl env) bndrs1
lvlExpr env (_, AnnLet bind body) = do
  (bind', new_env) <- lvlBind env bind
  body' <- lvlExpr new_env body
  return (Let bind' body')
lvlExpr env (_, AnnCase scrut case_bndr ty alts) = do
  scrut' <- lvlNonTailMFE env True scrut
  lvlCase env (freeVarsOf scrut) scrut' case_bndr ty alts

lvlNonTailExpr
  :: LevelEnv
  -> CoreExprWithFVs
  -> LvlM LevelledExpr
lvlNonTailExpr env expr = lvlExpr env expr

lvlApp
  :: LevelEnv
  -> CoreExprWithFVs
  -> (CoreExprWithFVs, [CoreExprWithFVs])
  -> LvlM LevelledExpr
lvlApp env orig_expr ((_, AnnVar fn), args)
  --  | fn `hasKey` runRWKey

  | floatOverSat env
  , arity > 0
  , arity < n_val_args
  = do rargs' <- mapM (lvlNonTailMFE env False) rargs
       lapp' <- lvlNonTailMFE env False lapp
       return (foldl' App lapp' rargs')
  | otherwise
  = do args' <- mapM (lvlMFE env False) args
       return (foldl' App (lookupVar env fn) args')
  where
    n_val_args = count (isValArg . deAnnotate) args
    arity = idArity fn

    (lapp, rargs) = left (n_val_args - arity) orig_expr []

    left 0 e rargs = (e, rargs)
    left n (_, AnnApp f a) rargs
      | isValArg (deAnnotate a) = left (n - 1) f (a : rargs)
      | otherwise = left n f (a : rargs)
    left  _ _ _ = panic "CSlash.Core.Opt.SetLevels.lvlExpr.left"

lvlApp env _ (fun, args) = do
  args' <- mapM (lvlNonTailMFE env False) args
  fun' <- lvlNonTailExpr env fun
  return (foldl' App fun' args')

-- type DCoreVarSets = (DKiVarSet Zk, DKiCoVarSet Zk, ... )
lvlCase
  :: LevelEnv
  -> DCoreVarSets
  -> LevelledExpr
  -> Id Zk
  -> Type Zk
  -> [CoreAltWithFVs]
  -> LvlM LevelledExpr
lvlCase env scrut_fvs scrut' case_bndr ty alts
  | [AnnAlt con@(DataAlt {}) bs body] <- alts
  , exprIsHNF (deTagExpr scrut')
  , not (isTopLvl dest_lvl)
  , not (floatTopLvlOnly env)
  , panic "nonLinear (varKind case_bndr)"
  = do (env1, (case_bndr' : bs')) <- cloneCaseBndrs env dest_lvl (case_bndr : bs)
       let rhs_env = extendCaseBndrEnv env1 case_bndr scrut'
       body' <- lvlMFE rhs_env True body
       let alt' = Alt con (map (stayPutLet dest_lvl) bs') body'
       return (Case scrut' (TB case_bndr' (FloatMe dest_lvl)) ty' [alt'])
  | otherwise
  = do let (alts_env1, [case_bndr']) = substAndLvlLetBndrs NonRecursive env incd_lvl [case_bndr]
           alts_env = extendCaseBndrEnv alts_env1 case_bndr scrut'
       alts' <- mapM (lvl_alt alts_env) alts
       return (Case scrut' case_bndr' ty' alts')
  where
    ty' = substTyUnchecked (le_subst env) ty

    incd_lvl = incMinorLvl (le_ctxt_lvl env)
    dest_lvl = maxFvLevel True (const True) env scrut_fvs

    lvl_alt alts_env (AnnAlt con bs rhs) = do
      rhs' <- lvlMFE new_env True rhs
      return (Alt con bs' rhs')
      where
        (new_env, bs') = substAndLvlLetBndrs NonRecursive alts_env incd_lvl bs

lvlNonTailMFE
  :: LevelEnv
  -> Bool
  -> CoreExprWithFVs
  -> LvlM LevelledExpr
lvlNonTailMFE env strict_ctxt ann_expr
  = lvlMFE env strict_ctxt ann_expr

lvlMFE
  :: LevelEnv
  -> Bool
  -> CoreExprWithFVs
  -> LvlM LevelledExpr
lvlMFE env _ (_, AnnType ty) = return (Type (substTyUnchecked (le_subst env) ty))
lvlMFE env _ (_, AnnKind ki) = return (Kind (substMonoKiUnchecked (le_subst env) ki))

lvlMFE env strict_ctxt (_, AnnTick t e) = do
  e' <- lvlMFE env strict_ctxt e
  let t' = substTickish (le_subst env) t
  return (Tick t' e')
  
lvlMFE env strict_ctxt (_, AnnCast e (_, co)) = do
  e' <- lvlMFE env strict_ctxt e
  return (Cast e' (panic "substTyCo (le_subst env) co"))
  
lvlMFE env strict_ctxt e@(_, AnnCase{})
  | strict_ctxt
  = lvlExpr env e
  
lvlMFE env strict_ctxt ann_expr
  | not float_me
    || floatTopLvlOnly env && not (isTopLvl dest_lvl)
    || hasFreeJoin env fvs
    || notWorthFloating expr abs_vars
  = lvlExpr env ann_expr

  | float_is_new_lam || exprIsTopLevelBindable expr expr_ty
  = do expr1 <- lvlFloatRhs abs_vars dest_lvl rhs_env NonRecursive
                is_bot_lam NotJoinPoint ann_expr
       var <- newLvlVar expr1 NotJoinPoint
       let var2 = annotateBotStr var float_n_lams mb_bot_str
       return (Let (NonRec (TB var2 (FloatMe dest_lvl)) expr1)
                   (mkAbsVarApps (Var var2) abs_vars))

  | otherwise
  = lvlExpr env ann_expr
  where
    expr = deAnnotate ann_expr
    expr_ty = exprType expr
    fvs = freeVarsOf ann_expr
    fvs_ty = varsOfType expr_ty
    is_bot_lam = isJust mb_bot_str
    is_function = isFunction ann_expr
    mb_bot_str = exprBotStrictness_maybe expr

    abs_vars = abstractVars dest_lvl env fvs
    dest_lvl = destLevel env fvs fvs_ty is_function is_bot_lam

    float_is_new_lam = float_n_lams > 0
    float_n_lams = count (isId . fst) abs_vars

    (rhs_env, abs_vars_w_lvls) = lvlLamBndrs env dest_lvl abs_vars

    float_me = saves_work || saves_alloc

    saves_work = escapes_value_lam
                 && not (exprIsHNF expr)
                 && not float_is_new_lam

    escapes_value_lam = dest_lvl `ltMajLvl` (le_ctxt_lvl env)

    saves_alloc = isTopLvl dest_lvl
                  && floatConsts env
                  && (not strict_ctxt
                      || exprIsHNF expr
                      || (is_bot_lam && escapes_value_lam))

hasFreeJoin :: LevelEnv -> DCoreVarSets -> Bool
hasFreeJoin env fvs
  = not (maxFvLevel False isJoinId env fvs == tOP_LEVEL)

annotateBotStr :: Id Zk -> Arity -> Maybe (Arity, DmdSig) -> Id Zk
annotateBotStr id n_extra mb_bot_str
  | Just (arity, str_sig) <- mb_bot_str
  = id `setIdArity` (arity + n_extra)
       `setIdDmdSig` prependArgsDmdSig n_extra str_sig
  | otherwise
  = id

notWorthFloating :: CoreExpr -> [(CoreBndr, a)] -> Bool
notWorthFloating e abs_vars = go e (count (isRuntimeVar . fst) abs_vars)
  where
    go (Var{}) n = n >= 0
    go (Lit lit) n = assert (n == 0) $ litIsTrivial lit
    go (Type{}) _ = True
    go (KiCo{}) _ = True
    go (Kind{}) _ = True
    go (App e arg) n
      | not (isRuntimeArg arg) = go e n
      | n == 0 = False
      | exprIsTrivial arg = go e (n - 1)
      | otherwise = False
    go (Tick t e) n = not (tickishIsCode t) && go e n
    go (Cast e _) n = go e n
    go _ _ = False

{- *********************************************************************
*                                                                      *
             Bindings
*                                                                      *
********************************************************************* -}

lvlBind
  :: LevelEnv
  -> CoreBindWithFVs
  -> LvlM (LevelledBind, LevelEnv)
lvlBind env (AnnNonRec bndr rhs)
  | not (wantToFloat env NonRecursive dest_lvl is_join is_top_bindable)
  = do rhs' <- lvlRhs env NonRecursive is_bot_lam mb_join_arity rhs
       let bind_lvl = incMinorLvl (le_ctxt_lvl env)
           (env', [bndr']) = substAndLvlLetBndrs NonRecursive env bind_lvl [bndr]
       return (NonRec bndr' rhs', env')

  | null abs_vars
  = do rhs' <- lvlFloatRhs [] dest_lvl env NonRecursive is_bot_lam NotJoinPoint rhs
       (env', [bndr']) <- cloneLetVars NonRecursive env dest_lvl [bndr]
       let bndr2 = annotateBotStr bndr' 0 mb_bot_str
       return (NonRec (TB bndr2 (FloatMe dest_lvl)) rhs', env')

  | otherwise
  = do rhs' <- lvlFloatRhs abs_vars dest_lvl env NonRecursive is_bot_lam NotJoinPoint rhs
       (env', [bndr']) <- newPolyBndrs dest_lvl env abs_vars [bndr]
       let bndr2 = annotateBotStr bndr' n_extra mb_bot_str
       return (NonRec (TB bndr2 (FloatMe dest_lvl)) rhs', env')

  where
    bndr_ty = varType bndr
    ty_fvs = varsOfType bndr_ty
    rhs_fvs = freeVarsOf rhs
    bind_fvs = rhs_fvs `unionDCoreVarSets` dIdFreeVars bndr
    abs_vars = abstractVars dest_lvl env bind_fvs
    dest_lvl = destLevel env bind_fvs ty_fvs (isFunction rhs) is_bot_lam

    deann_rhs = deAnnotate rhs
    mb_bot_str = exprBotStrictness_maybe deann_rhs
    is_bot_lam = not is_join && isJust mb_bot_str

    is_top_bindable = exprIsTopLevelBindable deann_rhs bndr_ty
    n_extra = count (isId . fst) abs_vars
    mb_join_arity = idJoinPointHood bndr
    is_join = isJoinPoint mb_join_arity

lvlBind env (AnnRec pairs)
  | not (wantToFloat env Recursive dest_lvl is_join is_top_bindable)
  = do let bind_lvl = incMinorLvl (le_ctxt_lvl env)
           (env', bndrs') = substAndLvlLetBndrs Recursive env bind_lvl bndrs
           lvl_rhs (b, r) = lvlRhs env' Recursive is_bot (idJoinPointHood b) r
       rhss' <- mapM lvl_rhs pairs
       return (Rec (bndrs' `zip` rhss'), env')

  | null abs_vars
  = do (new_env, new_bndrs) <- cloneLetVars Recursive env dest_lvl bndrs
       new_rhss <- mapM (do_rhs new_env) pairs
       return ( Rec ([TB b (FloatMe dest_lvl) | b <- new_bndrs] `zip` new_rhss)
              , new_env )

  | [(bndr, rhs)] <- pairs -- TODO (check GHC futures for this)
  , count (isRuntimeVar . fst) abs_vars > 1
  = do let (rhs_env, abs_vars_w_lvls) = lvlLamBndrs env dest_lvl abs_vars
           rhs_lvl = le_ctxt_lvl rhs_env

       (rhs_env', [new_bndr]) <- cloneLetVars Recursive rhs_env rhs_lvl [bndr]
       let (lam_bndrs, rhs_body) = collectAnnBndrs rhs
           (body_env1, lam_bndrs1) = substLamBndrsSL rhs_env' lam_bndrs
           (body_env2, lam_bndrs2) = lvlLamBndrs body_env1 rhs_lvl lam_bndrs1
       new_rhs_body <- lvlRhs body_env2 Recursive is_bot NotJoinPoint rhs_body

       (poly_env, [poly_bndr]) <- newPolyBndrs dest_lvl env abs_vars [bndr]

       return  (Rec [ (TB poly_bndr (FloatMe dest_lvl)
                      , mkCoreLams abs_vars_w_lvls $
                        mkCoreLams lam_bndrs2 $
                        Let (Rec [( TB new_bndr (StayPut rhs_lvl)
                                  , mkCoreLams lam_bndrs2 new_rhs_body )])
                             (mkAbsVarApps (Var new_bndr) lam_bndrs1)) ]
               , poly_env)

  | otherwise
  = do (new_env, new_bndrs) <- newPolyBndrs dest_lvl env abs_vars bndrs
       new_rhss <- mapM (do_rhs new_env) pairs
       return ( Rec ([TB b (FloatMe dest_lvl) | b <- new_bndrs] `zip` new_rhss)
              , new_env )

  where
    (bndrs, rhss) = unzip pairs
    is_join = isJoinId (head bndrs)

    is_fun = all isFunction rhss
    is_bot = False

    do_rhs env (_, rhs) = lvlFloatRhs abs_vars dest_lvl env Recursive is_bot NotJoinPoint rhs

    bind_fvs = panic "bind_fvs"

    ty_fvs = panic "ty_fvs"
    dest_lvl = destLevel env bind_fvs ty_fvs is_fun is_bot
    abs_vars = abstractVars dest_lvl env bind_fvs

    is_top_bindable = True

wantToFloat
  :: LevelEnv
  -> RecFlag
  -> Level
  -> Bool
  -> Bool
  -> Bool
wantToFloat env is_rec dest_lvl is_join is_top_bindable
  | not (profitableFloat env dest_lvl)
  = False
  | floatTopLvlOnly env && not (isTopLvl dest_lvl)
  = False
  | is_join
  = isTopLvl dest_lvl && (isRec is_rec || floatJoinsToTop (le_switches env))
  | otherwise
  = True

profitableFloat :: LevelEnv -> Level -> Bool
profitableFloat env dest_lvl
  = (dest_lvl `ltMajLvl` le_ctxt_lvl env)
    || (isTopLvl dest_lvl && floatConsts env)

lvlRhs
  :: LevelEnv
  -> RecFlag
  -> Bool
  -> JoinPointHood
  -> CoreExprWithFVs
  -> LvlM LevelledExpr
lvlRhs env rec_flag is_bot mb_join_arity expr
  = lvlFloatRhs [] (le_ctxt_lvl env) env rec_flag is_bot mb_join_arity expr

lvlFloatRhs
  :: [(OutBndr, Maybe CoreMonoKind)]
  -> Level
  -> LevelEnv
  -> RecFlag
  -> Bool
  -> JoinPointHood
  -> CoreExprWithFVs
  -> LvlM (Expr LevelledLamBndr LevelledLetBndr)
lvlFloatRhs abs_vars dest_lvl env is_rec is_bot mb_join_arity rhs = do
  body' <- if not is_bot && any (isRuntimeVar . fst) bndrs
           then lvlMFE body_env True body
           else lvlExpr body_env body
  return (mkCoreLams bndrs' body')
  where
    (bndrs, body) | JoinPoint join_arity <- mb_join_arity
                  = collectNAnnBndrs join_arity rhs
                  | otherwise
                  = collectAnnBndrs rhs
    (env1, bndrs1) = substLamBndrsSL env bndrs
    all_bndrs = abs_vars ++ bndrs1
    (body_env, bndrs') | JoinPoint{} <- mb_join_arity
                       = lvlJoinBndrs env1 dest_lvl is_rec all_bndrs
                       | otherwise
                       = lvlLamBndrs env1 dest_lvl all_bndrs

{- *********************************************************************
*                                                                      *
          Deciding floatability
*                                                                      *
********************************************************************* -}

substAndLvlLetBndrs :: RecFlag -> LevelEnv -> Level -> [InId] -> (LevelEnv, [LevelledLetBndr])
substAndLvlLetBndrs is_rec env lvl bndrs
  = lvlLetBndrs subst_env lvl subst_bndrs
  where
    (subst_env, subst_bndrs) = substLetBndrsSL is_rec env bndrs

substLetBndrsSL :: RecFlag -> LevelEnv -> [InId] -> (LevelEnv, [OutId])
substLetBndrsSL is_rec env@(LE { le_subst = subst, le_env = id_env }) bndrs
  = ( env { le_subst = subst'
          , le_env = foldl' add_id id_env (bndrs `zip` bndrs') }
    , bndrs' )
  where
    (subst', bndrs') = case is_rec of
                         NonRecursive -> substLetBndrs subst bndrs
                         Recursive -> substLetRecBndrs subst bndrs

-- substAndLvlLamBndrs :: LevelEnv -> Level -> [InBndr] -> (LevelEnv, [LevelledLamBndr])
-- substAndLvlLamBndrs env lvl bndrs
--   = lvlLamBndrs subst_env lvl subst_bndrs
--   where
--     (subst_env, subst_bndrs) = substLamBndrsSL env bndrs

substLamBndrsSL
  :: LevelEnv
  -> [(InBndr, Maybe CoreMonoKind)]
  -> (LevelEnv, [(OutBndr, Maybe CoreMonoKind)])
substLamBndrsSL env@(LE { le_subst = subst, le_env = id_env }) bndrs
  = ( env { le_subst = subst'
          , le_env = foldl' add_bndr id_env (bndrs `zip` bndrs') }
    , bndrs' )
  where
    (subst', bndrs') = substLamBndrs subst bndrs

lvlLamBndrs :: LevelEnv -> Level -> [(OutBndr, a)] -> (LevelEnv, [(LevelledLamBndr, a)])
lvlLamBndrs env@(LE { le_lvl_env = lvl_env }) lvl bndrs
  = ( env { le_ctxt_lvl = new_lvl
          , le_lvl_env = addLamLvls new_lvl lvl_env bndrs }
    , map (stayPutLam new_lvl) bndrs )
  where
    new_lvl | any is_major bndrs = incMajorLvl lvl
            | otherwise = incMinorLvl lvl
    is_major (bndr, _) = not (isOneShotBndr bndr)

lvlLetBndrs :: LevelEnv -> Level -> [OutId] -> (LevelEnv, [LevelledLetBndr])
lvlLetBndrs env@(LE { le_lvl_env = lvl_env }) new_lvl bndrs
  = ( env { le_ctxt_lvl = new_lvl
          , le_lvl_env = addLetLvls new_lvl lvl_env bndrs }
    , map (stayPutLet new_lvl) bndrs )

lvlJoinBndrs
  :: LevelEnv
  -> Level
  -> RecFlag
  -> [(OutBndr, Maybe CoreMonoKind)]
  -> (LevelEnv, [(LevelledLamBndr, Maybe CoreMonoKind)])
lvlJoinBndrs env lvl is_rec bndrs
  = lvlLamBndrs env new_lvl bndrs
  where
    new_lvl | isRec is_rec = incMajorLvl lvl
            | otherwise = incMinorLvl lvl

stayPutLet :: Level -> OutId -> LevelledLetBndr
stayPutLet new_lvl bndr = TB bndr (StayPut new_lvl)

stayPutLam :: Level -> (OutBndr, a) -> (LevelledLamBndr, a)
stayPutLam new_lvl (bndr, a) = (TB bndr (StayPut new_lvl), a)

destLevel
  :: LevelEnv
  -> DCoreVarSets
  -> (TyVarSet Zk, KiCoVarSet Zk, KiVarSet Zk)
  -> Bool
  -> Bool
  -> Level
destLevel env fvs fvs_ty is_function is_bot
  | isTopLvl max_fv_id_level
  = tOP_LEVEL

  | is_bot
  = as_far_as_poss

  | floatLams env
  , is_function
  = as_far_as_poss

  | otherwise
  = max_fv_id_level

  where
    max_fv_id_level = maxFvLevel False (const True) env fvs

    as_far_as_poss = maxFvLevel' False env fvs_ty

isFunction :: CoreExprWithFVs -> Bool
isFunction (_, AnnLam (Core.Id _) _ _) = True
isFunction (_, AnnLam _ _ e) = isFunction e
isFunction _ = False

{- *********************************************************************
*                                                                      *
           Free-To-Level Monad
*                                                                      *
********************************************************************* -}

-- Put the type syn in CSlash.Core
type CoreVarEnv a = ( IdEnv Zk a
                    , TyCoVarEnv Zk a
                    , TyVarEnv Zk a
                    , KiCoVarEnv Zk a
                    , KiVarEnv Zk a )

data LevelEnv = LE
  { le_switches :: FloatOutSwitches
  , le_ctxt_lvl :: Level
  , le_lvl_env :: CoreVarEnv Level
  , le_subst :: CoreSubst
  , le_env :: IdEnv Zk ([OutId], LevelledExpr) -- don't care about the [OutId]s, just their max level
  }

leTCvEnv :: LevelEnv -> TyCoVarEnv Zk Level
leTCvEnv (LE { le_lvl_env = (_, env, _, _, _) }) = env

leTvEnv :: LevelEnv -> TyVarEnv Zk Level
leTvEnv (LE { le_lvl_env = (_, _, env, _, _) }) = env

leKCvEnv :: LevelEnv -> KiCoVarEnv Zk Level
leKCvEnv (LE { le_lvl_env = (_, _, _, env, _) }) = env

leKvEnv :: LevelEnv -> KiVarEnv Zk Level
leKvEnv (LE { le_lvl_env = (_, _, _, _, env) }) = env

initialEnv :: FloatOutSwitches -> CoreProgram -> LevelEnv
initialEnv float_lams binds
  = LE { le_switches = float_lams
       , le_ctxt_lvl = tOP_LEVEL
       , le_lvl_env = (emptyVarEnv, emptyVarEnv, emptyVarEnv, emptyVarEnv, emptyVarEnv)
       , le_subst = subst_toplvl
       , le_env = emptyVarEnv }
  where
    subst_toplvl = extendTermSubstInScopeBndrs emptySubst binds

addLetLvl :: Level -> CoreVarEnv Level -> OutId -> CoreVarEnv Level
addLetLvl dest_lvl (id, tco, ty, kco, ki) v'
  = (extendVarEnv id v' dest_lvl, tco, ty, kco, ki)

addLamLvl :: Level -> CoreVarEnv Level -> (OutBndr, a) -> CoreVarEnv Level
addLamLvl dest_lvl (id, tco, ty, kco, ki) (Core.Id v', _)
  = (extendVarEnv id v' dest_lvl, tco, ty, kco, ki)
addLamLvl dest_lvl (id, tco, ty, kco, ki) (Core.Tv v', _)
  = (id, tco, extendVarEnv ty v' dest_lvl, kco, ki)
addLamLvl dest_lvl (id, tco, ty, kco, ki) (Core.KCv v', _)
  = (id, tco, ty, extendVarEnv kco v' dest_lvl, ki)
addLamLvl dest_lvl (id, tco, ty, kco, ki) (Core.Kv v', _)
  = (id, tco, ty, kco, extendVarEnv ki v' dest_lvl)

addLetLvls :: Level -> CoreVarEnv Level -> [OutId] -> CoreVarEnv Level
addLetLvls dest_lvl env vs = foldl' (addLetLvl dest_lvl) env vs

addLamLvls :: Level -> CoreVarEnv Level -> [(OutBndr, a)] -> CoreVarEnv Level
addLamLvls dest_lvl env vs = foldl' (addLamLvl dest_lvl) env vs

floatLams :: LevelEnv -> Bool
floatLams le = floatOutAllLambdas (le_switches le)

floatConsts :: LevelEnv -> Bool
floatConsts le = floatOutConstants (le_switches le)

floatOverSat :: LevelEnv -> Bool
floatOverSat le = floatOutOverSatApps (le_switches le)

floatTopLvlOnly :: LevelEnv -> Bool
floatTopLvlOnly le = floatToTopLevelOnly (le_switches le)

extendCaseBndrEnv
  :: LevelEnv
  -> CoreId
  -> Expr LevelledLamBndr LevelledLetBndr
  -> LevelEnv
extendCaseBndrEnv le@(LE { le_subst = subst, le_env = id_env }) case_bndr (Var scrut_var)
  = le { le_subst = extendIdSubst subst case_bndr (Var scrut_var)
       , le_env = add_id id_env (case_bndr, scrut_var) }
extendCaseBndrEnv env _ _ = env

maxFvLevel
  :: Bool
  -> (CoreId -> Bool)
  -> LevelEnv
  -> DCoreVarSets
  -> Level
maxFvLevel all_vars max_me env (ids, tcvs, tvs, kcvs, kvs)
  | all_vars
  = nonDetStrictFoldDVarSet (maxIn max_me env) tOP_LEVEL ids `maxLvl`
    nonDetStrictFoldDVarSet (maxInOther (leTCvEnv env)) tOP_LEVEL tcvs `maxLvl`
    nonDetStrictFoldDVarSet (maxInOther (leTvEnv env)) tOP_LEVEL tvs `maxLvl`
    nonDetStrictFoldDVarSet (maxInOther (leKCvEnv env)) tOP_LEVEL kcvs `maxLvl`
    nonDetStrictFoldDVarSet (maxInOther (leKvEnv env)) tOP_LEVEL kvs
  | otherwise
  = nonDetStrictFoldDVarSet (maxIn max_me env) tOP_LEVEL ids `maxLvl`
    nonDetStrictFoldDVarSet (maxInOther (leTCvEnv env)) tOP_LEVEL tcvs `maxLvl`
    nonDetStrictFoldDVarSet (maxInOther (leKCvEnv env)) tOP_LEVEL kcvs

maxFvLevel'
  :: Bool
  -> LevelEnv
  -> (TyVarSet Zk, KiCoVarSet Zk, KiVarSet Zk)
  -> Level
maxFvLevel' all_vars env (tvs, kcvs, kvs)
  | all_vars
  = nonDetStrictFoldUniqSet (maxInOther (leTvEnv env)) tOP_LEVEL tvs `maxLvl`
    nonDetStrictFoldUniqSet (maxInOther (leKCvEnv env)) tOP_LEVEL kcvs `maxLvl`
    nonDetStrictFoldUniqSet (maxInOther (leKvEnv env)) tOP_LEVEL kvs
  | otherwise
  = nonDetStrictFoldUniqSet (maxInOther (leKCvEnv env)) tOP_LEVEL kcvs

maxIn :: (CoreId -> Bool) -> LevelEnv -> InId -> Level -> Level
maxIn max_me (LE { le_lvl_env = (lvl_env, _, _, _, _), le_env = id_env }) in_var lvl
  = case lookupVarEnv id_env in_var of
      Just (abs_vars, _) -> foldr max_out lvl abs_vars
      Nothing -> max_out in_var lvl
  where
    max_out out_var lvl
      | max_me out_var = case lookupVarEnv lvl_env out_var of
                           Just lvl' -> maxLvl lvl' lvl
                           Nothing -> lvl
      | otherwise = lvl
 
maxInOther :: Uniquable a => VarEnv a Level -> a -> Level -> Level
maxInOther env var lvl
  = case lookupVarEnv env var of
      Just lvl' -> maxLvl lvl' lvl
      Nothing -> lvl

--type syn to CSlash.Core
type DCoreVarSets = (DIdSet Zk, DTyCoVarSet Zk, DTyVarSet Zk, DKiCoVarSet Zk, DKiVarSet Zk)

unionDCoreVarSets :: DCoreVarSets -> DCoreVarSets -> DCoreVarSets
unionDCoreVarSets (id1, tcv1, tv1, kcv1, kv1) (id2, tcv2, tv2, kcv2, kv2)
  = ( unionDVarSet id1 id2
    , unionDVarSet tcv1 tcv2
    , unionDVarSet tv1 tv2
    , unionDVarSet kcv1 kcv2
    , unionDVarSet kv1 kv2 )


lookupBndrLvl :: CoreVarEnv Level -> CoreBndr -> Maybe Level
lookupBndrLvl (env, _, _, _, _)(Core.Id v) = lookupVarEnv env v 
lookupBndrLvl (_, _, env, _, _) (Tv v) = lookupVarEnv env v 
lookupBndrLvl (_, _, _, env, _) (KCv v) = lookupVarEnv env v 
lookupBndrLvl (_, _, _, _, env) (Kv v) = lookupVarEnv env v 

lookupVar :: LevelEnv -> CoreId -> LevelledExpr
lookupVar le v = case lookupVarEnv (le_env le) v of
                   Just (_, expr) -> expr
                   _ -> Var v

abstractVars
  :: Level
  -> LevelEnv
  -> DCoreVarSets
  -> [(CoreBndr, Maybe CoreMonoKind)]
abstractVars dest_lvl (LE { le_subst = subst, le_lvl_env = lvl_env }) in_fvs
  = map zap $
    filter abstract_me $
    to_bndrs $
    -- TODO: make sure we've already closed over kinds
    substDCoreVarSets subst in_fvs
  where
    abstract_me v = case lookupBndrLvl lvl_env v of
                      Just lvl -> dest_lvl `ltLvl` lvl
                      Nothing -> False

    zap (Core.Id v) = warnPprTrace (isStableUnfolding (idUnfolding v))
                      "absVarsOf: discarding info on" (ppr v) $
                      (Core.Id $ setIdInfo v vanillaIdInfo, Just (BIKi LKd)) -- TODO: check linear
    zap v = (v, Nothing)

    to_bndrs (ids, tcvs, tvs, kcvs, kvs)
      = assertPpr (isEmptyDVarSet tcvs) (text "abstractVars has TyCoVars" <+> ppr tcvs)
        fmap Kv (dVarSetElems kvs) ++
        fmap KCv (dVarSetElems kcvs) ++
        fmap Tv (dVarSetElems tvs) ++
        fmap Core.Id (dVarSetElems ids)

type LvlM result = UniqSM result

initLvl :: UniqSupply -> UniqSM a -> a
initLvl = initUs_

newPolyBndrs
  :: Level
  -> LevelEnv
  -> [(OutBndr, Maybe CoreMonoKind)]
  -> [InId]
  -> LvlM (LevelEnv, [OutId])
newPolyBndrs dest_lvl env@(LE { le_lvl_env = lvl_env, le_subst = subst, le_env = id_env })
             abs_vars bndrs
  = do
      uniqs <- getUniquesM
      let new_bndrs = zipWith mk_poly_bndr bndrs uniqs
          bndr_prs = bndrs `zip` new_bndrs
          env' = env { le_lvl_env = addLetLvls dest_lvl lvl_env new_bndrs
                     , le_subst = foldl' add_subst subst bndr_prs
                     , le_env = panic "foldl' add_id id_env bndr_prs" }
      return (env', new_bndrs)
  where
    add_subst env (v, v') = extendIdSubst env v (mkAbsVarApps (Var v') abs_vars)
    add_id env (v, v') = extendVarEnv env v ((v' : panic "abs_vars"), mkAbsVarApps (Var v') abs_vars)

    mk_poly_bndr bndr uniq
      = transferPolyIdInfo bndr abs_vars $
        transfer_join_info bndr $
        mkSysLocal str uniq poly_ty
      where
        str = fsLit "poly_" `appendFS` occNameFS (getOccName bndr)
        poly_ty = mkLamTypes abs_vars (substTyUnchecked subst (varType bndr))

    dest_is_top = isTopLvl dest_lvl
    transfer_join_info bndr new_bndr
      | JoinPoint join_arity <- idJoinPointHood bndr
      , not dest_is_top
      = new_bndr `asJoinId` (join_arity + length abs_vars)
      | otherwise
      = new_bndr

newLvlVar
  :: LevelledExpr
  -> JoinPointHood
  -> LvlM CoreId
newLvlVar lvld_rhs join_arity_maybe = do
  uniq <- getUniqueM
  return (add_join_info (mk_id uniq rhs_ty))
  where
    add_join_info var = var `asJoinId_maybe` join_arity_maybe
    de_tagged_rhs = deTagExpr lvld_rhs
    rhs_ty = exprType de_tagged_rhs

    mk_id uniq rhs_ty = mkSysLocal (mkFastString "lvl") uniq rhs_ty

cloneCaseBndrs :: LevelEnv -> Level -> [CoreId] -> LvlM (LevelEnv, [CoreId])
cloneCaseBndrs env@(LE { le_subst = subst, le_lvl_env = lvl_env, le_env = id_env }) new_lvl vs
  = do (subst', vs') <- cloneIdBndrs subst vs
       let env' = env { le_lvl_env = addLetLvls new_lvl lvl_env vs'
                      , le_subst = subst'
                      , le_env = foldl' add_id id_env (vs `zip` vs') }
       return (env', vs')

cloneLetVars
  :: RecFlag
  -> LevelEnv
  -> Level
  -> [InId]
  -> LvlM (LevelEnv, [OutId])
cloneLetVars is_rec env@(LE { le_subst = subst, le_lvl_env = lvl_env, le_env = id_env }) dest_lvl vs
  = do let vs1 = map zap vs
       (subst', vs2) <- case is_rec of
         NonRecursive -> cloneIdBndrs subst vs1
         Recursive -> cloneRecIdBndrs subst vs1
       let prs = vs `zip` vs2
           env' = env { le_lvl_env = addLetLvls dest_lvl lvl_env vs2
                      , le_subst = subst'
                      , le_env = foldl' add_id id_env prs }
       return (env', vs2)
  where
    zap :: CoreId -> CoreId
    zap v = zap_join (floatifyIdDemandInfo v)

    zap_join | isTopLvl dest_lvl = zapJoinId
             | otherwise = id

add_id
  :: IdEnv Zk ([CoreId], LevelledExpr)
  -> (CoreId, CoreId)
  -> IdEnv Zk ([CoreId], LevelledExpr)
add_id id_env (v, v1) = extendVarEnv id_env v ([v1], Var v1)

add_bndr
  :: IdEnv Zk ([CoreId], LevelledExpr)
  -> ((CoreBndr, a), (CoreBndr, a))
  -> IdEnv Zk ([CoreId], LevelledExpr)
add_bndr id_env ((Core.Id v, _), (Core.Id v1, _))
  = extendVarEnv id_env v ([v1], Var v1)
add_bndr id_env _ = id_env
