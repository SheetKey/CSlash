{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}

{-# OPTIONS_GHC -Werror=unused-local-binds #-}

module CSlash.Core.Opt.Simplify.Utils where

import Prelude hiding ((<>))

import CSlash.Core as C
import CSlash.Core.Make
-- import CSlash.Types.Literal ( isLitRubbish )
import CSlash.Core.Opt.Simplify.Env
import CSlash.Core.Opt.Simplify.Inline( smallEnoughToInline )
import CSlash.Core.Opt.Stats ( Tick(..) )
import qualified CSlash.Core.Subst as Subst
import CSlash.Core.Subst (CoreSubst)
import CSlash.Core.Ppr
import CSlash.Core.Type.Ppr ( pprParendType )
import CSlash.Core.FVs
import CSlash.Core.Utils
import CSlash.Core.Rules( RuleEnv, getRules )
import CSlash.Core.Opt.Arity
import CSlash.Core.Unfold
import CSlash.Core.Unfold.Make
import CSlash.Core.Opt.Simplify.Monad
import CSlash.Core.Type
-- import CSlash.Core.DataCon ( dataConWorkId, isNullaryRepDataCon )
import CSlash.Core.Kind
import CSlash.Core.Opt.ConstantFold

import CSlash.Types.Name hiding (varName)
import CSlash.Types.Var
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.Tickish
import CSlash.Types.Demand
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Types.Basic

import CSlash.Data.OrdList ( isNilOL )
import CSlash.Data.FastString ( fsLit )

import CSlash.Utils.Misc
import CSlash.Utils.Monad
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Trace
import CSlash.Types.Unique.Supply

import Control.Monad    ( when )
import Data.List        ( sortBy )
import CSlash.Types.Name.Env
import Data.Graph

{- *********************************************************************
*                                                                      *
               BindContext
*                                                                      *
********************************************************************* -}

data BindContext
  = BC_Let TopLevelFlag RecFlag
  | BC_Join RecFlag SimplCont

bindContextLevel :: BindContext -> TopLevelFlag
bindContextLevel (BC_Let top_lvl _) = top_lvl
bindContextLevel BC_Join{} = NotTopLevel

bindContextRec :: BindContext -> RecFlag
bindContextRec (BC_Let _ rec_flag) = rec_flag
bindContextRec (BC_Join rec_flag _) = rec_flag

isJoinBC :: BindContext -> Bool
isJoinBC BC_Let{} = False
isJoinBC BC_Join{} = True

{- *********************************************************************
*                                                                      *
               SimplCont and DupFlag
*                                                                      *
********************************************************************* -}

data SimplCont
  = Stop OutType CallCtxt SubDemand

  | CastIt
    { sc_co :: OutTypeCoercion
    , sc_opt :: Bool
    , sc_cont :: SimplCont }

  | ApplyToVal
    { sc_dup :: DupFlag
    , sc_hole_ty :: OutType
    , sc_arg :: InExpr
    , sc_env :: StaticEnv
    , sc_cont :: SimplCont }

  | ApplyToTy
    { sc_arg_ty :: OutType
    , sc_hole_ty :: OutType
    , sc_cont :: SimplCont }

  | ApplyToKiCo
    { sc_arg_kico :: OutKindCoercion
    , sc_hole_ty :: OutType
    , sc_cont :: SimplCont }

  | ApplyToKi
    { sc_arg_ki :: OutMonoKind
    , sc_hole_ty :: OutType
    , sc_cont :: SimplCont }
    

  | Select
    { sc_dup :: DupFlag
    , sc_bndr :: InId
    , sc_alts :: [InAlt]
    , sc_env :: StaticEnv
    , sc_cont :: SimplCont }

  | StrictBind
    { sc_dup :: DupFlag
    , sc_from :: FromWhat
    , sc_bndr :: InId
    , sc_body :: InExpr
    , sc_env :: StaticEnv
    , sc_cont :: SimplCont }

  | StrictArg
    { sc_dup :: DupFlag
    , sc_fun :: ArgInfo
    , sc_fun_ty :: OutType
    , sc_cont :: SimplCont }

  | TickIt CoreTickish SimplCont

type StaticEnv = SimplEnv

data FromWhat = FromLet | FromBeta

data DupFlag
  = NoDup
  | Simplified
  | OkToDup

isSimplified :: DupFlag -> Bool
isSimplified NoDup = False
isSimplified _ = True

perhapsSubstTy :: DupFlag -> StaticEnv -> CoreType -> CoreType
perhapsSubstTy dup env ty
  | isSimplified dup = ty
  | otherwise = substTy env ty

instance Outputable DupFlag where
  ppr OkToDup = text "ok"
  ppr NoDup = text "nodup"
  ppr Simplified = text "simpl"

instance Outputable SimplCont where
  ppr (Stop ty interesting eval_sd)
    = text "Stop" <> brackets (sep $ punctuate comma pps) <+> ppr ty
    where pps = [ppr interesting] ++ [ppr eval_sd | eval_sd /= topSubDmd]

  ppr CastIt{ sc_co = co, sc_cont = cont }
    = (text "CastIt" <+> pprOptTyCo co) $$ ppr cont

  ppr (TickIt t cont)
    = (text "TickIt" <+> ppr t) $$ ppr cont

  ppr ApplyToTy{ sc_arg_ty = ty, sc_cont = cont }
    = (text "ApplyToTy" <+> pprParendType ty) $$ ppr cont

  ppr ApplyToKiCo{ sc_arg_kico = co, sc_cont = cont }
    = (text "ApplyToKiCo" <+> ppr co) $$ ppr cont

  ppr ApplyToKi{ sc_arg_ki = ki, sc_cont = cont }
    = (text "ApplyToKi" <+> pprParendMonoKind ki) $$ ppr cont

  ppr ApplyToVal{ sc_arg = arg, sc_dup = dup, sc_cont = cont, sc_hole_ty = hole_ty }
    = (hang (text "ApplyToVal" <+> ppr dup <+> text "hole" <+> ppr hole_ty)
       2 (pprParendExpr arg))
      $$ ppr cont

  ppr StrictBind{ sc_bndr = b, sc_cont = cont }
    = (text "StrictBind" <+> ppr b) $$ ppr cont

  ppr StrictArg{ sc_fun = ai, sc_cont = cont }
    = (text "StrictArg" <+> ppr (ai_fun ai)) $$ ppr cont

  ppr Select{ sc_dup = dup, sc_bndr = bndr, sc_alts = alts, sc_cont = cont }
    = (text "Select" <+> ppr dup <+> ppr bndr) $$
      whenPprDebug (nest 2 $ ppr alts) $$ ppr cont

{- *********************************************************************
*                                                                      *
               ArgInfo and ArgSpec
*                                                                      *
********************************************************************* -}

data ArgInfo = ArgInfo
  { ai_fun :: OutId
  , ai_args :: [ArgSpec]
  , ai_rewrite :: RewriteCall
  , ai_encl :: Bool
  , ai_dmds :: [Demand]
  , ai_discs :: [Int]
  }

data RewriteCall
  = TryRules FullArgCount [CoreRule]
  | TryInlining
  | TryNothing

data ArgSpec
  = ValArg
    { as_dmd :: Demand
    , as_arg :: OutExpr
    , as_hole_ty :: OutType }
  | TyArg
    { as_arg_ty :: OutType
    , as_hole_ty :: OutType }
  | KiCoArg
    { as_arg_kico :: OutKindCoercion
    , as_hole_ty :: OutType }
  | KiArg
    { as_arg_ki :: OutMonoKind
    , as_hole_ty :: OutType }
  | CastBy OutTypeCoercion

instance Outputable ArgInfo where
  ppr ArgInfo{ ai_fun = fun, ai_args = args, ai_dmds = dmds }
    = text "ArgInfo" <+> braces
      (sep [ text "fun =" <+> ppr fun
           , text "dmds(first 10) =" <+> ppr (take 10 dmds)
           , text "args =" <+> ppr args ])

instance Outputable ArgSpec where
  ppr ValArg{ as_arg = arg } = text "ValArg" <+> ppr arg
  ppr TyArg{ as_arg_ty = ty } = text "TyArg" <+> ppr ty
  ppr KiCoArg{ as_arg_kico = kico } = text "KiCoArg" <+> ppr kico
  ppr KiArg{ as_arg_ki = ki } = text "KiArg" <+> ppr ki
  ppr (CastBy c) = text "CastBy" <+> ppr c

addValArgTo :: ArgInfo -> OutExpr -> OutType -> ArgInfo
addValArgTo ai arg hole_ty
  | ArgInfo { ai_dmds = dmd:dmds, ai_discs = _:discs, ai_rewrite = new } <- ai
  , let arg_spec = ValArg { as_arg = arg, as_hole_ty = hole_ty, as_dmd = dmd }
  = ai { ai_args = arg_spec : ai_args ai
       , ai_dmds = dmds
       , ai_discs = discs
       , ai_rewrite = decArgCount new }
  | otherwise
  = pprPanic "addValArgTo" (ppr ai $$ ppr arg)

addTyArgTo :: ArgInfo -> OutType -> OutType -> ArgInfo
addTyArgTo ai arg_ty hole_ty = ai { ai_args = arg_spec : ai_args ai
                                  , ai_rewrite = decArgCount (ai_rewrite ai) }
  where arg_spec = TyArg { as_arg_ty = arg_ty, as_hole_ty = hole_ty }

addKiCoArgTo :: ArgInfo -> OutKindCoercion -> OutType -> ArgInfo
addKiCoArgTo ai arg_co hole_ty = ai { ai_args = arg_spec : ai_args ai
                                    , ai_rewrite = decArgCount (ai_rewrite ai) }
  where arg_spec = KiCoArg { as_arg_kico = arg_co, as_hole_ty = hole_ty }

addKiArgTo :: ArgInfo -> OutMonoKind -> OutType -> ArgInfo
addKiArgTo ai arg_ki hole_ty = ai { ai_args = arg_spec : ai_args ai
                                  , ai_rewrite = decArgCount (ai_rewrite ai) }
  where arg_spec = KiArg { as_arg_ki = arg_ki, as_hole_ty = hole_ty }

addCastTo :: ArgInfo -> OutTypeCoercion -> ArgInfo
addCastTo ai co = ai { ai_args = CastBy co : ai_args ai }

argInfoAppArgs :: [ArgSpec] -> [OutExpr]
argInfoAppArgs [] = []
argInfoAppArgs (CastBy{} : _) = []
argInfoAppArgs (ValArg { as_arg = arg } : as) = arg : argInfoAppArgs as
argInfoAppArgs (TyArg { as_arg_ty = ty } : as) = Type ty : argInfoAppArgs as
argInfoAppArgs (KiCoArg { as_arg_kico = kico } : as) = KiCo kico : argInfoAppArgs as
argInfoAppArgs (KiArg { as_arg_ki = ki } : as) = Kind ki : argInfoAppArgs as

pushSimplifiedArgs :: SimplEnv -> [ArgSpec] -> SimplCont -> SimplCont
pushSimplifiedArgs env args cont = foldr (pushSimplifiedArg env) cont args

pushSimplifiedRevArgs :: SimplEnv -> [ArgSpec] -> SimplCont -> SimplCont
pushSimplifiedRevArgs env args cont = foldl' (\k a -> pushSimplifiedArg env a k) cont args

pushSimplifiedArg :: SimplEnv -> ArgSpec -> SimplCont -> SimplCont
pushSimplifiedArg _ TyArg{ as_arg_ty = arg_ty, as_hole_ty = hole_ty } cont
  = ApplyToTy { sc_arg_ty = arg_ty, sc_hole_ty = hole_ty, sc_cont = cont }
pushSimplifiedArg _ KiCoArg{ as_arg_kico = arg_kico, as_hole_ty = hole_ty } cont
  = ApplyToKiCo { sc_arg_kico = arg_kico, sc_hole_ty = hole_ty, sc_cont = cont }
pushSimplifiedArg _ KiArg{ as_arg_ki = arg_ki, as_hole_ty = hole_ty } cont
  = ApplyToKi { sc_arg_ki = arg_ki, sc_hole_ty = hole_ty, sc_cont = cont }
pushSimplifiedArg env ValArg{ as_arg = arg, as_hole_ty = hole_ty } cont
  = ApplyToVal { sc_arg = arg, sc_env = env, sc_dup = Simplified
               , sc_hole_ty = hole_ty, sc_cont = cont }
pushSimplifiedArg _ (CastBy c) cont
  = CastIt { sc_co = c, sc_cont = cont, sc_opt = True }

argInfoExpr :: OutId -> [ArgSpec] -> OutExpr
argInfoExpr fun rev_args
  = go rev_args
  where
    go [] = Var fun
    go (ValArg{ as_arg = arg } : as) = go as `App` arg
    go (TyArg{ as_arg_ty = ty } : as) = go as `App` Type ty
    go (KiCoArg{ as_arg_kico = kico } : as) = go as `App` KiCo kico
    go (KiArg{ as_arg_ki = ki } : as) = go as `App` Kind ki
    go (CastBy co : as) = mkCast (go as) co

decArgCount :: RewriteCall -> RewriteCall
decArgCount (TryRules n rules) = TryRules (n - 1) rules
decArgCount rew = rew

mkRewriteCall :: CoreId -> RuleEnv -> RewriteCall
mkRewriteCall fun rule_env
  | not (null rules) = TryRules n_required rules
  | canUnfold unf = TryInlining
  | otherwise = TryNothing
  where
    n_required = maximum (map ruleArity rules)
    rules = getRules rule_env fun
    unf = idUnfolding fun

{- *********************************************************************
*                                                                      *
                Functions on SimplCont
*                                                                      *
********************************************************************* -}

mkBoringStop :: OutType -> SimplCont
mkBoringStop ty = Stop ty BoringCtxt topSubDmd

mkRhsStop :: OutType -> RecFlag -> Demand -> SimplCont
mkRhsStop ty is_rec bndr_dmd = Stop ty (RhsCtxt is_rec) (subDemandIfEvaluated bndr_dmd)

mkStrictArgStop :: OutType -> ArgInfo -> SimplCont
mkStrictArgStop ty fun_info = Stop ty (strictArgContext fun_info) arg_sd
  where
    arg_sd = subDemandIfEvaluated (head (ai_dmds fun_info))

contIsRhs :: SimplCont -> Maybe RecFlag
contIsRhs (Stop _ (RhsCtxt is_rec) _ ) = Just is_rec
contIsRhs CastIt{ sc_cont = k } = contIsRhs k
contIsRhs _ = Nothing

contIsStop :: SimplCont -> Bool
contIsStop Stop{} = True
contIsStop _ = False

contIsDupable :: SimplCont -> Bool
contIsDupable Stop{} = True
contIsDupable ApplyToTy{ sc_cont = k } = contIsDupable k
contIsDupable ApplyToKiCo{ sc_cont = k } = contIsDupable k
contIsDupable ApplyToKi{ sc_cont = k } = contIsDupable k
contIsDupable ApplyToVal{ sc_dup = OkToDup } = True
contIsDupable Select{ sc_dup = OkToDup } = True
contIsDupable StrictArg{ sc_dup = OkToDup } = True
contIsDupable CastIt{ sc_cont = k } = contIsDupable k
contIsDupable _ = False

contIsTrivial :: SimplCont -> Bool
contIsTrivial Stop{} = True
contIsTrivial ApplyToTy{ sc_cont = k } = contIsTrivial k
contIsTrivial ApplyToKiCo{ sc_cont = k } = contIsTrivial k
contIsTrivial ApplyToKi{ sc_cont = k } = contIsTrivial k
contIsTrivial CastIt{ sc_cont = k } = contIsTrivial k
contIsTrivial _ = False

contResultType :: SimplCont -> OutType
contResultType (Stop ty _ _) = ty
contResultType CastIt{ sc_cont = k } = contResultType k
contResultType StrictBind{ sc_cont = k } = contResultType k
contResultType StrictArg{ sc_cont = k } = contResultType k
contResultType Select{ sc_cont = k } = contResultType k
contResultType ApplyToTy{ sc_cont = k } = contResultType k
contResultType ApplyToKiCo{ sc_cont = k } = contResultType k
contResultType ApplyToKi{ sc_cont = k } = contResultType k
contResultType ApplyToVal{ sc_cont = k } = contResultType k
contResultType (TickIt _ k) = contResultType k

contHoleType :: SimplCont -> OutType
contHoleType (Stop ty _ _) = ty
contHoleType (TickIt _ k) = contHoleType k
contHoleType CastIt{ sc_co = co } = tycoercionLType co
contHoleType StrictBind{ sc_bndr = b, sc_dup = dup, sc_env = se }
  = perhapsSubstTy dup se (varType b)
contHoleType StrictArg{ sc_fun_ty = ty } = funArgTy ty
contHoleType ApplyToTy{ sc_hole_ty = ty } = ty
contHoleType ApplyToKiCo{ sc_hole_ty = ty } = ty
contHoleType ApplyToKi{ sc_hole_ty = ty } = ty
contHoleType ApplyToVal{ sc_hole_ty = ty } = ty
contHoleType Select{ sc_dup = d, sc_bndr = b, sc_env = se }
  = perhapsSubstTy d se (varType b)

countArgs :: SimplCont -> Int
countArgs ApplyToTy{ sc_cont = cont } = 1 + countArgs cont
countArgs ApplyToKiCo{ sc_cont = cont } = 1 + countArgs cont
countArgs ApplyToKi{ sc_cont = cont } = 1 + countArgs cont
countArgs ApplyToVal{ sc_cont = cont } = 1 + countArgs cont
countArgs CastIt{ sc_cont = cont } = countArgs cont
countArgs _ = 0

countValArgs :: SimplCont -> Int
countValArgs ApplyToTy{ sc_cont = cont } = countValArgs cont
countValArgs ApplyToKiCo{ sc_cont = cont } = countValArgs cont
countValArgs ApplyToKi{ sc_cont = cont } = countValArgs cont
countValArgs ApplyToVal{ sc_cont = cont } = 1 + countValArgs cont
countValArgs CastIt{ sc_cont = cont } = countValArgs cont
countValArgs _ = 0

contArgs :: SimplCont -> (Bool, [ArgSummary], SimplCont)
contArgs cont
  | lone cont = (True, [], cont)
  | otherwise = go [] cont
  where
    lone ApplyToTy{} = False
    lone ApplyToKiCo{} = False
    lone ApplyToKi{} = False
    lone ApplyToVal{} = False
    lone CastIt{} = False
    lone _ = True

    go args ApplyToVal{sc_arg = arg, sc_env = se, sc_cont = k }
      = go (is_interesting arg se : args) k
    go args ApplyToTy{ sc_cont = k } = go args k
    go args ApplyToKiCo{ sc_cont = k } = go args k
    go args ApplyToKi{ sc_cont = k } = go args k
    go args CastIt{ sc_cont = k } = go args k
    go args k = (False, reverse args, k)

    is_interesting arg se = interestingArg se arg

contEvalContext :: SimplCont -> SubDemand
contEvalContext k = case k of
  Stop _ _ sd -> sd
  TickIt _ k -> contEvalContext k
  CastIt{ sc_cont = k } -> contEvalContext k
  ApplyToTy{ sc_cont = k } -> contEvalContext k
  ApplyToKiCo{ sc_cont = k } -> contEvalContext k
  ApplyToKi{ sc_cont = k } -> contEvalContext k
  ApplyToVal{} -> pprPanic "contEvalContext" (ppr k)
  StrictArg{ sc_fun = fun_info } -> subDemandIfEvaluated (head (ai_dmds fun_info))
  StrictBind{ sc_bndr = bndr } -> subDemandIfEvaluated (idDemandInfo bndr)
  Select{} -> topSubDmd

mkArgInfo :: SimplEnv -> RuleEnv -> CoreId -> SimplCont -> ArgInfo
mkArgInfo env rule_base fun cont
  | n_val_args <- idArity fun
  = ArgInfo { ai_fun = fun
            , ai_args = []
            , ai_rewrite = fun_rewrite
            , ai_encl = False
            , ai_dmds = vanilla_dmds
            , ai_discs = vanilla_discounts }

  | otherwise
  = ArgInfo { ai_fun = fun
            , ai_args = []
            , ai_rewrite = fun_rewrite
            , ai_encl = fun_has_rules || contHasRules cont
            , ai_dmds = arg_dmds
            , ai_discs = arg_discounts }
  where
    n_val_args = countValArgs cont
    fun_rewrite = mkRewriteCall fun rule_base
    fun_has_rules = case fun_rewrite of
      TryRules{} -> True
      _ -> False

    vanilla_discounts = repeat 0
    arg_discounts = case idUnfolding fun of
      CoreUnfolding { uf_guidance = UnfIfGoodArgs { ug_args = discounts } }
        -> discounts ++ vanilla_discounts
      _ -> vanilla_discounts

    vanilla_dmds = repeat topDmd

    arg_dmds
      | not (seInline env)
      = vanilla_dmds
      | otherwise
      = case splitDmdSig (idDmdSig fun) of
          (demands, result_info)
            | not (demands `lengthExceeds` n_val_args)
            -> if isDeadEndDiv result_info then demands else demands ++ vanilla_dmds
            | otherwise
            -> warnPprTrace True "More demands than arity"
               (ppr fun <+> ppr (idArity fun) <+> ppr n_val_args <+> ppr demands) $
               vanilla_dmds

{- *********************************************************************
*                                                                      *
                Interesting arguments
*                                                                      *
********************************************************************* -}

strictArgContext :: ArgInfo -> CallCtxt
strictArgContext ArgInfo{ ai_encl = encl_rules, ai_discs = discs }
  | encl_rules = RuleArgCtxt
  | disc:_ <- discs, disc > 0 = DiscArgCtxt
  | otherwise = RhsCtxt NonRecursive

interestingCallContext :: SimplEnv -> SimplCont -> CallCtxt
interestingCallContext env cont
  = interesting cont
  where
    interesting Select{ sc_alts = alts, sc_bndr = case_bndr }
      | not (seCaseCase env)
      = BoringCtxt
      | [Alt _ bs _] <- alts
      , all isDeadBinder bs
      , not (isDeadBinder case_bndr)
      = RhsCtxt NonRecursive
      | otherwise = CaseCtxt
    interesting ApplyToVal{} = ValAppCtxt
    interesting StrictArg{ sc_fun = fun } = strictArgContext fun
    interesting StrictBind{} = BoringCtxt
    interesting (Stop _ cci _) = cci
    interesting (TickIt _ k) = interesting k
    interesting ApplyToTy{ sc_cont = k } = interesting k
    interesting ApplyToKiCo{ sc_cont = k } = interesting k
    interesting ApplyToKi{ sc_cont = k } = interesting k
    interesting CastIt{ sc_cont = k } = interesting k

contHasRules :: SimplCont -> Bool
contHasRules cont = go cont
  where
    go ApplyToVal{ sc_cont = cont } = go cont
    go ApplyToTy{ sc_cont = cont } = go cont
    go ApplyToKiCo{ sc_cont = cont } = go cont
    go ApplyToKi{ sc_cont = cont } = go cont
    go CastIt{ sc_cont = cont } = go cont
    go StrictArg{ sc_fun = fun } = ai_encl fun
    go (Stop _ RuleArgCtxt _) = True
    go (TickIt _ c) = go c
    go Select{} = False
    go StrictBind{} = False
    go Stop{} = False

interestingArg :: SimplEnv -> CoreExpr -> ArgSummary
interestingArg env e = go env 0 e
  where
    go env n (Var v) = case substId env v of
      DoneId v' -> go_var n v'
      DoneEx e _ -> go (zapSubstEnv env) n e
      ContEx ids tcvs tvs kcvs kvs e -> go (setSubstEnv env ids tcvs tvs kcvs kvs) n e

    go _ _ (Lit l) = panic "Lit"
    go _ _ Type{} = TrivArg
    go _ _ KiCo{} = TrivArg
    go _ _ Kind{} = TrivArg
    go env n (App fn (Type _)) = go env n fn
    go env n (App fn (KiCo _)) = go env n fn
    go env n (App fn (Kind _)) = go env n fn
    go env n (App fn _) = go env (n + 1) fn
    go env n (Tick _ a) = go env n a
    go env n (Cast e _) = go env n e
    go env n (Lam v _ e)
      | isNonRuntimeVar v = go env n e
      | n > 0 = NonTrivArg
      | otherwise = ValueArg
    go _ _ Case{} = NonTrivArg
    go env n (Let b e) = case go env' n e of
      ValueArg -> ValueArg
      _ -> NonTrivArg
      where
        env' = env `addNewInScopeIds` bindersOf b

    go_var n v
      | isConLikeId v = ValueArg
      | idArity v > n = ValueArg
      | n > 0 = NonTrivArg
      | otherwise
      = case idUnfolding v of
          OtherCon [] -> NonTrivArg
          OtherCon _ -> ValueArg
          CoreUnfolding{ uf_cache = cache }
            | uf_is_conlike cache -> ValueArg
            | uf_is_value cache -> NonTrivArg
            | otherwise -> TrivArg
          NoUnfolding -> TrivArg

{- *********************************************************************
*                                                                      *
                SimplMode
*                                                                      *
********************************************************************* -}

updModeForStableUnfoldings :: Activation -> SimplMode -> SimplMode
updModeForStableUnfoldings unf_act current_mode
  = current_mode { sm_phase = phaseFromActivation unf_act
                 , sm_eta_expand = False
                 , sm_inline = True }
  where
    phaseFromActivation (ActiveAfter _ n) = Phase n
    phaseFromActivation _ = InitialPhase

updModeForRules :: SimplMode -> SimplMode
updModeForRules current_mode
  = current_mode { sm_phase = InitialPhase
                 , sm_inline = False
                 , sm_rules = False
                 , sm_cast_swizzle = False
                 , sm_eta_expand = False }

getUnfoldingInRuleMatch :: SimplEnv -> InScopeEnv
getUnfoldingInRuleMatch env
  = ISE in_scope id_unf
  where
    in_scope = seInScope env
    phase = sePhase env
    id_unf = whenActiveUnfoldingFun (isActive phase)

activeRule :: SimplMode -> Activation -> Bool
activeRule mode
  | not (sm_rules mode) = \_ -> False
  | otherwise = isActive (sm_phase mode)

{- *********************************************************************
*                                                                      *
                preInlineUnconditionally
*                                                                      *
********************************************************************* -}

preInlineUnconditionally
  :: SimplEnv
  -> TopLevelFlag
  -> InId
  -> InExpr
  -> StaticEnv
  -> Maybe SimplEnv
preInlineUnconditionally env top_lvl bndr rhs rhs_env
  | not pre_inline_unconditionally = Nothing
  | not active = Nothing
  | isTopLevel top_lvl && isDeadEndId bndr = Nothing
  | isExitJoinId bndr = Nothing
  | not (one_occ (idOccInfo bndr)) = Nothing
  | not (isStableUnfolding unf) = Just $! (extend_subst_with rhs)
  | not (isInlinePragma inline_prag)
  , Just inl <- maybeUnfoldingTemplate unf = Just $! (extend_subst_with inl)
  | otherwise = Nothing
  where
    unf = idUnfolding bndr
    extend_subst_with inl_rhs = extendIdSubst env bndr $! (mkContEx rhs_env inl_rhs)

    one_occ IAmDead = True
    one_occ OneOcc{ occ_n_br = 1, occ_in_lam = NotInsideLam }
      = isNotTopLevel top_lvl || early_phase
    one_occ OneOcc{ occ_n_br = 1, occ_in_lam = IsInsideLam, occ_int_cxt = IsInteresting }
      = canInlineInLam rhs
    one_occ _ = False

    pre_inline_unconditionally = sePreInline env
    active = isActive (sePhase env) (inlinePragmaActivation inline_prag)
    inline_prag = idInlinePragma bndr

    canInlineInLam (Lit _) = True
    canInlineInLam (Lam b _ e) = isRuntimeVar b || canInlineInLam e
    canInlineInLam (Tick t e) = not (tickishIsCode t) && canInlineInLam e
    canInlineInLam _ = False

    early_phase = sePhase env /= FinalPhase

{- *********************************************************************
*                                                                      *
                postInlineUnconditionally
*                                                                      *
********************************************************************* -}

postInlineUnconditionally
  :: SimplEnv
  -> BindContext
  -> InId
  -> OutId
  -> OutExpr
  -> Bool
postInlineUnconditionally env bind_cxt old_bndr bndr rhs
  | not active = False
  | isWeakLoopBreaker occ_info = False
  | isStableUnfolding unfolding = False
  | isTopLevel (bindContextLevel bind_cxt) = False
  | exprIsTrivial rhs = True
  | BC_Join{} <- bind_cxt = False
  | otherwise
  = case occ_info of
      OneOcc { occ_in_lam = in_lam, occ_int_cxt = int_cxt, occ_n_br = n_br }
        | n_br >= 100 -> False
        | n_br == 1, NotInsideLam <- in_lam -> True
        | is_demanded -> False
        | otherwise -> work_ok in_lam int_cxt && smallEnoughToInline uf_opts unfolding
      IAmDead -> True
      _ -> False
  where
    work_ok NotInsideLam _ = True
    work_ok IsInsideLam IsInteresting = isCheapUnfolding unfolding
    work_ok IsInsideLam NotInteresting = False

    is_demanded = True -- TODO
    occ_info = idOccInfo old_bndr
    unfolding = idUnfolding bndr
    uf_opts = seUnfoldingOpts env
    phase = sePhase env
    active = isActive phase (idInlineActivation bndr)

{- *********************************************************************
*                                                                      *
                Rebuilding a lambda
*                                                                      *
********************************************************************* -}

rebuildLam
  :: SimplEnv
  -> [(OutBndr, Maybe OutMonoKind)]
  -> OutExpr
  -> SimplCont
  -> SimplM OutExpr
rebuildLam _ [] body _ = return body
rebuildLam env bndrs@(bndr:_) body cont
  = {-# SCC "rebuildLam" #-} try_eta bndrs body
  where
    rec_ids = seRecIds env
    in_scope = getInScope env
    mb_rhs = contIsRhs cont

    eval_sd = contEvalContext cont

    try_eta :: [(OutBndr, Maybe OutMonoKind)] -> OutExpr -> SimplM OutExpr
    try_eta bndrs body
      | seDoEtaReduction env
      , Just etad_lam <- tryEtaReduce rec_ids bndrs body eval_sd
      = do tick (EtaReduction $ fst bndr)
           return etad_lam

      | Nothing <- mb_rhs
      , seEtaExpand env
      , any (isRuntimeVar . fst) bndrs
      , Just body_arity <- exprEtaExpandArity (seArityOpts env) body
      = do tick (EtaExpansion $ fst bndr)
           let body' = etaExpandAT in_scope body_arity body
           traceSmpl "eta expand" 
             $ vcat [ text "before" <+> ppr body
                    , text "after" <+> ppr body' ]
           return $ mk_lams bndrs body'
      | otherwise
      = return (mk_lams bndrs body)

    mk_lams :: [(OutBndr, Maybe OutMonoKind)] -> OutExpr -> OutExpr
    mk_lams bndrs body@Lam{}
      = mk_lams (bndrs ++ bndrs1) body1
      where
        (bndrs1, body1) = collectBinders body
    mk_lams bndrs (Tick t expr)
      | tickishFloatable t
      = mkTick t (mk_lams bndrs expr)
    mk_lams bndrs (Cast body co)
      | seCastSwizzle env
      , not (any bad bndrs)
      = mkCast (mkCoreLams bndrs body) (panic "mkPiCos bndrs co")
      where
        bad bndr = panic "unfinished"
    mk_lams bndrs body = mkCoreLams bndrs body

{- *********************************************************************
*                                                                      *
              Eta expansion
*                                                                      *
********************************************************************* -}

tryEtaExpandRhs
  :: SimplEnv
  -> BindContext
  -> OutId
  -> OutExpr
  -> SimplM (ArityType, OutExpr)
tryEtaExpandRhs env bind_cxt bndr rhs
  | seEtaExpand env
  , wantEtaExpansion rhs
  , do_eta_expand
  = assertPpr (not (isJoinBC bind_cxt)) (ppr bndr) $ do
      tick (EtaExpansion $ C.Id bndr)
      return (arity_type, etaExpandAT in_scope arity_type rhs)
  | otherwise
  = return (arity_type, rhs)
  where
    in_scope = getInScope env
    arity_opts = seArityOpts env
    is_rec = bindContextRec bind_cxt
    (do_eta_expand, arity_type) = findRhsArity arity_opts is_rec bndr rhs

wantEtaExpansion :: CoreExpr -> Bool
wantEtaExpansion (Cast e _) = wantEtaExpansion e
wantEtaExpansion (Tick _ e) = wantEtaExpansion e
wantEtaExpansion (Lam b k e) | isNonRuntimeVar b = wantEtaExpansion e
wantEtaExpansion (App e _) = wantEtaExpansion e
wantEtaExpansion Var{} = False
wantEtaExpansion Lit{} = False
wantEtaExpansion _ = True

{- *********************************************************************
*                                                                      *
              Floating lets out of big lambdas
*                                                                      *
********************************************************************* -}

abstractFloats
  :: UnfoldingOpts
  -> TopLevelFlag
  -> [OutBndr]
  -> SimplFloats
  -> OutExpr
  -> SimplM ([OutBind], OutExpr)
abstractFloats uf_opts top_lvl main_tkcvs floats body
  = assert (notNull body_floats) $
    assert (isNilOL (sfJoinFloats floats)) $
    do let sccs = concatMap to_sccs body_floats
       (subst, float_binds) <- mapAccumLM abstract empty_subst sccs
       return (float_binds, Subst.substExpr subst body)
  where
    (main_kvs, main_kcvs, main_tvs) = foldr go ([], [], []) main_tkcvs
      where
        go
          :: OutBndr
          -> ([OutKiVar], [OutKiCoVar], [OutTyVar])
          -> ([OutKiVar], [OutKiCoVar], [OutTyVar])
        go C.Id{} _ = panic "abstractFloats bad bndrs" (ppr main_tkcvs)
        go (Tv tv) (k, c, t) = (k, c, tv : t)
        go (KCv kcv) (k, c, t) = (k, kcv : c, t)
        go (Kv kv) (k, c, t) = (kv : k, c, t)

    is_top_lvl = isTopLevel top_lvl
    body_floats = letFloatBinds (sfLetFloats floats)
    empty_subst = Subst.mkEmptyTermSubstIS (sfInScope floats, emptyInScopeSet, emptyInScopeSet
                                           , emptyInScopeSet, emptyInScopeSet)

    to_sccs :: OutBind -> [SCC (CoreId, CoreExpr, CoreVarSets)]
    to_sccs (NonRec id e) = [AcyclicSCC (id, e, emptyCoreVarSets)]
    to_sccs (Rec prs) = sccs
      where
        (ids, rhss) = unzip prs
        sccs = depAnal (\(id, _, _) -> [getName id])
                       (\(_, _, (fvs, _, _, _, _))
                        -> nonDetStrictFoldVarSet ((:) . getName) [] fvs)
                       (zip3 ids rhss (map exprFreeVars rhss))

    abstract :: CoreSubst -> SCC (CoreId, CoreExpr, CoreVarSets) -> SimplM (CoreSubst, OutBind)
    abstract subst (AcyclicSCC (id, rhs, _)) = do
      (poly_id1, poly_app) <- mk_poly1 vs_here id
      let (poly_id2, poly_rhs) = mk_poly2 poly_id1 vs_here rhs'
          !subst' = Subst.extendIdSubst subst id poly_app
      return (subst', NonRec poly_id2 poly_rhs)
      where
        rhs' = Subst.substExpr subst rhs
        vs_here = choose_nonruntime (exprFreeVars rhs')

    abstract subst (CyclicSCC trpls) = do
      (poly_ids, poly_apps) <- mapAndUnzipM (mk_poly1 vs_here) ids
      let subst' = Subst.extendSubstList subst ((C.Id <$> ids) `zip` poly_apps)
          poly_pairs = [ mk_poly2 poly_id vs_here rhs'
                       | (poly_id, rhs) <- poly_ids `zip` rhss
                       , let rhs' = Subst.substExpr subst' rhs ]
      return (subst', Rec poly_pairs)
      where
        (ids, rhss, _) = unzip3 trpls

        vs_here = choose_nonruntime (mapUnionCoreVarSets get_bind_fvs trpls)

        get_bind_fvs (id, _, rhs_fvs) = fixup (varsOfType (varType id)) `unionCoreVarSets`
                                        get_rec_rhs_vs rhs_fvs
          where fixup (tvs, kcvs, kvs) = (emptyVarSet, emptyVarSet, tvs, kcvs, kvs)

        get_rec_rhs_vs rhs_fvs = nonDetStrictFoldCoreVarSets
                                 from_ids from_tcvs from_tvs from_kcvs from_kvs
                                 emptyCoreVarSets rhs_fvs

        from_ids var free_vs
          | Just poly_app <- Subst.lookupIdSubst_maybe subst var
          = exprFreeVars poly_app `unionCoreVarSets` free_vs
          | otherwise
          = free_vs

        from_tcvs _ free_vs = free_vs

        from_tvs var (ids, tcvs, tvs, kcvs, kvs)
          = (ids, tcvs, extendVarSet tvs var, kcvs, kvs)

        from_kcvs var (ids, tcvs, tvs, kcvs, kvs)
          = (ids, tcvs, tvs, extendVarSet kcvs var, kvs) -- TODO: check

        from_kvs var (ids, tcvs, tvs, kcvs, kvs)
          = (ids, tcvs, tvs, kcvs, extendVarSet kvs var)


    choose_nonruntime (_, tcvs, tvs, kcvs, kvs)
      = assertPpr (isEmptyVarSet tcvs) (text "choose_nonruntime" <+> ppr tcvs)
      ( filter (`elemVarSet` kvs) main_kvs
      , filter (`elemVarSet` kcvs) main_kcvs
      , filter (`elemVarSet` tvs) main_tvs )

    mk_poly1 :: ([CoreKiVar], [CoreKiCoVar], [CoreTyVar]) -> CoreId -> SimplM (CoreId, CoreExpr)
    mk_poly1 vs_here@(kvs_here, kcvs_here, tvs_here) var = do
      uniq <- getUniqueM
      let poly_name = setNameUnique (varName var) uniq
          poly_ty = mkBigLamTys kvs_here $
                    mkForAllKiCos kcvs_here $
                    mkInfForAllTys tvs_here $
                    (varType var)
          poly_id = transferPolyIdInfo var ((, ()) <$> ((Kv <$> kvs_here) ++
                                                       (KCv <$> kcvs_here) ++
                                                       (Tv <$> tvs_here))) $
                    mkLocalId poly_name poly_ty
      return (poly_id, Var poly_id `mkKiApps` (mkKiVarKis kvs_here)
                                   `mkKiCoApps` (mkKiCoVarCos kcvs_here)
                                   `mkTyApps` (mkTyVarTys tvs_here))

    mk_poly2
      :: CoreId -> ([CoreKiVar], [CoreKiCoVar], [CoreTyVar]) -> CoreExpr ->  (CoreId, CoreExpr)
    mk_poly2 poly_id (kvs_here, kcvs_here, tvs_here) rhs
      = (poly_id `setIdUnfolding` unf, poly_rhs)
      where
        poly_rhs = mkCoreLams ((, Nothing) <$>
                               ((Kv <$> kvs_here) ++ (KCv <$> kcvs_here) ++ (Tv <$> tvs_here)))
                   rhs
        unf = mkUnfolding uf_opts VanillaSrc is_top_lvl False False poly_rhs Nothing
    
{- *********************************************************************
*                                                                      *
                prepareAlts
*                                                                      *
********************************************************************* -}

prepareAlts :: OutExpr -> InId -> [InAlt] -> SimplM ([AltCon], [InAlt])
prepareAlts = panic "prepareAlts"

{- *********************************************************************
*                                                                      *
                mkCase
*                                                                      *
********************************************************************* -}

mkCase :: SimplMode -> OutExpr -> OutId -> OutType -> [OutAlt] -> SimplM OutExpr
mkCase = panic "mkCase"


isExitJoinId :: CoreId -> Bool
isExitJoinId id = isJoinId id
                  && isOneOcc (idOccInfo id)
                  && occ_in_lam (idOccInfo id) == IsInsideLam
