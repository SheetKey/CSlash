{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Werror=unused-local-binds #-}

module CSlash.Core.Opt.Simplify.Env where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Core.Opt.Coercion ( OptCoercionOpts )
import CSlash.Core.Opt.Arity (ArityOpts(..))
import CSlash.Core.Opt.Simplify.Monad
import CSlash.Core as C
import CSlash.Core.Utils
import CSlash.Core.Unfold
import CSlash.Core.Subst hiding
  ( substIdBndr, substIdType
  , substTyVarBndr, substKiCoVarBndr, substKiVarBndr)
import qualified CSlash.Core.Subst as Subst
import CSlash.Core.Kind
import CSlash.Core.Make ( mkWildValBinder, mkCoreLet )
import CSlash.Core.Type
import CSlash.Core.Type.FVs (noFreeVarsOfType)
import qualified CSlash.Core.Type as Type

import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Var.Id as Id
import CSlash.Types.Basic
import CSlash.Types.Unique.FM      ( pprUniqFM )

import CSlash.Data.OrdList
import CSlash.Data.Graph.UnVar

import CSlash.Builtin.Types
import CSlash.Platform ( Platform )

import CSlash.Utils.Monad
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc

import Data.List ( intersperse, mapAccumL )

{- *********************************************************************
*                                                                      *
                        SimplEnv
*                                                                      *
********************************************************************* -}

data SimplEnv = SimplEnv
  {
    -- Static environment
    seMode :: !SimplMode

  , seIdSubst :: SimplIdSubst
  , seTCvSubst :: CoreTCvSubstEnv
  , seTvSubst :: CoreTvSubstEnv
  , seKCvSubst :: CoreKCvSubstEnv
  , seKvSubst :: CoreKvSubstEnv

  , seRecIds :: !UnVarSet

    -- Dynamic environment
  , seInScope :: !TermSubstInScope

  , seCaseDepth :: !Int

  , seInlineDepth :: !Int
  }

seIdInScope :: SimplEnv -> InScopeSet CoreId
seIdInScope env = case seInScope env of
  (ids, _, _, _, _) -> ids

seArityOpts :: SimplEnv -> ArityOpts
seArityOpts env = sm_arity_opts (seMode env)

seCaseCase :: SimplEnv -> Bool
seCaseCase = sm_case_case . seMode

seCaseFolding :: SimplEnv -> Bool
seCaseFolding = sm_case_folding . seMode

seCaseMerge :: SimplEnv -> Bool
seCaseMerge = sm_case_merge . seMode

seCastSwizzle :: SimplEnv -> Bool
seCastSwizzle = sm_cast_swizzle . seMode

seDoEtaReduction :: SimplEnv -> Bool
seDoEtaReduction = sm_do_eta_reduction . seMode

seEtaExpand :: SimplEnv -> Bool
seEtaExpand = sm_eta_expand . seMode

seFloatEnable :: SimplEnv -> FloatEnable
seFloatEnable = sm_float_enable . seMode

seInline :: SimplEnv -> Bool
seInline = sm_inline . seMode

seNames :: SimplEnv -> [String]
seNames = sm_names . seMode

seOptCoercionOpts :: SimplEnv -> OptCoercionOpts
seOptCoercionOpts = sm_co_opt_opts . seMode

sePhase :: SimplEnv -> CompilerPhase
sePhase = sm_phase . seMode

sePlatform :: SimplEnv -> Platform
sePlatform = smPlatform . seMode

sePreInline :: SimplEnv -> Bool
sePreInline = sm_pre_inline . seMode

seRuleOpts :: SimplEnv -> RuleOpts
seRuleOpts = sm_rule_opts . seMode

seRules :: SimplEnv -> Bool
seRules = sm_rules . seMode

seUnfoldingOpts :: SimplEnv -> UnfoldingOpts
seUnfoldingOpts = sm_uf_opts . seMode

data SimplMode = SimplMode
  { sm_phase :: !CompilerPhase
  , sm_names :: ![String]
  , sm_rules :: !Bool
  , sm_inline :: !Bool
  , sm_eta_expand :: !Bool
  , sm_cast_swizzle :: Bool
  , sm_uf_opts :: !UnfoldingOpts
  , sm_case_case :: !Bool
  , sm_pre_inline :: !Bool
  , sm_float_enable :: !FloatEnable
  , sm_do_eta_reduction :: !Bool
  , sm_arity_opts :: !ArityOpts
  , sm_rule_opts :: !RuleOpts
  , sm_case_folding :: !Bool
  , sm_case_merge :: !Bool
  , sm_co_opt_opts :: !OptCoercionOpts
  }

instance Outputable SimplMode where
  ppr SimplMode{ sm_phase = p
               , sm_names = ss
               , sm_rules = r
               , sm_inline = i
               , sm_cast_swizzle = cs
               , sm_eta_expand = eta
               , sm_case_case = cc }
    = text "SimplMode" <+> 
      braces (sep [ text "Phase =" <+> ppr p <+>
                     brackets (text (concat $ intersperse "," ss)) <> comma
                   , pp_flag i (text "inline") <> comma
                   , pp_flag r (text "rules") <> comma
                   , pp_flag eta (text "eta_expand") <> comma
                   , pp_flag cs (text "cast_swizzle") <> comma
                   , pp_flag cc (text "case-of-case") ])
    where
      pp_flag f s = ppUnless f (text "no") <+> s

smPlatform :: SimplMode -> Platform
smPlatform = roPlatform . sm_rule_opts

data FloatEnable
  = FloatDisabled
  | FloatNestedOnly
  | FloatEnabled

data SimplFloats = SimplFloats
  { sfLetFloats :: LetFloats
  , sfJoinFloats :: JoinFloats
  , sfInScope :: InScopeSet CoreId
  }

instance Outputable SimplFloats where
  ppr SimplFloats{ sfLetFloats = lf, sfJoinFloats = jf, sfInScope = is }
    = text "SimplFloats" <+> braces 
      (vcat [ text "lets:" <+> ppr lf
           , text "joins:" <+> ppr jf
           , text "in_scope:" <+> ppr is ])

emptyFloats :: SimplEnv -> SimplFloats
emptyFloats env = SimplFloats
  { sfLetFloats = emptyLetFloats
  , sfJoinFloats = emptyJoinFloats
  , sfInScope = case seInScope env of
                  (ids, _, _, _, _) -> ids
  }

isEmptyFloats :: SimplFloats -> Bool
isEmptyFloats SimplFloats{ sfLetFloats = LetFloats fs _, sfJoinFloats = js }
  = assertPpr (isNilOL js) (ppr js) $ isNilOL fs

pprSimplEnv :: SimplEnv -> SDoc
pprSimplEnv env
  = vcat [ text "IdSubst:" <+> id_subst_doc
         , text "TCvSubst:" <+> ppr (seTCvSubst env)
         , text "TvSubst:" <+> ppr (seTvSubst env)
         , text "KCvSubst:" <+> ppr (seKCvSubst env)
         , text "KvSubst:" <+> ppr (seKvSubst env)
         , text "InScope:" <+> in_scope_vars_doc
         ]
  where
    id_subst_doc = pprUniqFM ppr (seIdSubst env)
    in_scope_vars_doc = case seInScope env of
      (ids, tcvs, tvs, kcvs, kvs) ->
        vcat [ pprVarSet (getInScopeVars ids) (vcat . map ppr_one)
             , pprVarSet (getInScopeVars tcvs) (vcat . map ppr)
             , pprVarSet (getInScopeVars tvs) (vcat . map ppr)
             , pprVarSet (getInScopeVars kcvs) (vcat . map ppr)
             , pprVarSet (getInScopeVars kvs) (vcat . map ppr) ]
    ppr_one :: CoreId -> SDoc
    ppr_one v = ppr v <+> ppr (idUnfolding v)

type SimplIdSubst = IdEnv Zk SimplSR

data SimplSR
  = DoneEx OutExpr JoinPointHood
  | DoneId OutId
  | ContEx SimplIdSubst
           CoreTCvSubstEnv
           CoreTvSubstEnv
           CoreKCvSubstEnv
           CoreKvSubstEnv
           InExpr

instance Outputable SimplSR where
  ppr (DoneId v) = text "DoneId" <+> ppr v
  ppr (DoneEx e mj) = text "DoneEx" <> pp_mj <+> ppr e
    where pp_mj = case mj of
                    NotJoinPoint -> empty
                    JoinPoint n -> parens (int n)
  ppr (ContEx _ _ _ _ _ e) = vcat [ text "ContEx" <+> ppr e ]

mkSimplEnv :: SimplMode -> SimplEnv
mkSimplEnv mode = SimplEnv
  { seMode = mode
  , seInScope = init_in_scope
  , seIdSubst = emptyVarEnv
  , seTCvSubst = emptyVarEnv
  , seTvSubst = emptyVarEnv
  , seKCvSubst = emptyVarEnv
  , seKvSubst = emptyVarEnv
  , seRecIds = emptyUnVarSet
  , seCaseDepth = 0
  , seInlineDepth = 0
  }
 
init_in_scope :: TermSubstInScope
init_in_scope = ( mkInScopeSet (unitVarSet $
                                mkWildValBinder (mkTyConApp unitTyCon [Embed (BIKi UKd)]))
                , emptyInScopeSet
                , emptyInScopeSet
                , emptyInScopeSet
                , emptyInScopeSet )

updMode :: (SimplMode -> SimplMode) -> SimplEnv -> SimplEnv
updMode upd env = let mode = upd $! (seMode env)
                  in env { seMode = mode }

bumpCaseDepth :: SimplEnv -> SimplEnv
bumpCaseDepth env = env { seCaseDepth = seCaseDepth env + 1 }

reSimplifying :: SimplEnv -> Bool
reSimplifying SimplEnv{ seInlineDepth = n } = n > 0

extendIdSubst :: SimplEnv -> CoreId -> SimplSR -> SimplEnv
extendIdSubst env@SimplEnv{ seIdSubst = subst } var res
  = env { seIdSubst = extendVarEnv subst var res }

extendTCvSubst :: SimplEnv -> CoreTyCoVar -> CoreTypeCoercion -> SimplEnv
extendTCvSubst env@SimplEnv{ seTCvSubst = subst } var res
  = env { seTCvSubst = extendVarEnv subst var res }

extendTvSubst :: SimplEnv -> CoreTyVar -> CoreType -> SimplEnv
extendTvSubst env@SimplEnv{ seTvSubst = subst } var res
  = env { seTvSubst = extendVarEnv subst var res }

extendKCvSubst :: SimplEnv -> CoreKiCoVar -> CoreKindCoercion -> SimplEnv
extendKCvSubst env@SimplEnv{ seKCvSubst = subst } var res
  = env { seKCvSubst = extendVarEnv subst var res }

extendKvSubst :: SimplEnv -> CoreKiVar -> CoreMonoKind -> SimplEnv
extendKvSubst env@SimplEnv{ seKvSubst = subst } var res
  = env { seKvSubst = extendVarEnv subst var res }

getInScope :: SimplEnv -> TermSubstInScope
getInScope = seInScope

setInScopeSet :: SimplEnv -> TermSubstInScope -> SimplEnv
setInScopeSet env in_scope = env { seInScope = in_scope }

setInScopeFromE :: SimplEnv -> SimplEnv -> SimplEnv
setInScopeFromE rhs_env here_env = rhs_env { seInScope = seInScope here_env }

setInScopeFromF :: SimplEnv -> SimplFloats -> SimplEnv
setInScopeFromF env floats
  = env { seInScope = ( sfInScope floats
                      , emptyInScopeSet
                      , emptyInScopeSet
                      , emptyInScopeSet
                      , emptyInScopeSet ) }

addNewInScopeIds :: SimplEnv -> [CoreId] -> SimplEnv
addNewInScopeIds env@SimplEnv{ seInScope = (in_scope, tcvs, tvs, kcvs, kvs)
                             , seIdSubst = id_subst } vs 
  = let !in_scope1 = in_scope `extendInScopeSetList` vs
        !id_subst1 = id_subst `delVarEnvList` vs
    in env { seInScope = (in_scope1, tcvs, tvs, kcvs, kvs)
           , seIdSubst = id_subst1 }

modifyInScope :: SimplEnv -> CoreId -> SimplEnv
modifyInScope env@SimplEnv{ seInScope = (in_scope, tcvs, tvs, kcvs, kvs) } v
  = env { seInScope = (extendInScopeSet in_scope v, tcvs, tvs, kcvs, kvs) }

enterRecGroupRHSs
  :: SimplEnv
  -> [CoreId]
  -> (SimplEnv -> SimplM (r, SimplEnv))
  -> SimplM (r, SimplEnv)
enterRecGroupRHSs env bndrs k = do
  (r, env'') <- k env{ seRecIds = extendUnVarSetList bndrs (seRecIds env) }
  return (r, env'' { seRecIds = seRecIds env })

zapSubstEnv :: SimplEnv -> SimplEnv
zapSubstEnv env@SimplEnv{ seInlineDepth = n }
  = env { seIdSubst = emptyVarEnv
        , seTCvSubst = emptyVarEnv
        , seTvSubst = emptyVarEnv
        , seKCvSubst = emptyVarEnv
        , seKvSubst = emptyVarEnv
        , seInlineDepth = n + 1 }

setSubstEnv
  :: SimplEnv
  -> SimplIdSubst
  -> CoreTCvSubstEnv
  -> CoreTvSubstEnv
  -> CoreKCvSubstEnv
  -> CoreKvSubstEnv
  -> SimplEnv
setSubstEnv env ids tcvs tvs kcvs kvs
  = env { seIdSubst = ids
        , seTCvSubst = tcvs
        , seTvSubst = tvs
        , seKCvSubst = kcvs
        , seKvSubst = kvs }        

mkContEx :: SimplEnv -> InExpr -> SimplSR
mkContEx SimplEnv{ seIdSubst = ids
                 , seTCvSubst = tcvs
                 , seTvSubst = tvs
                 , seKCvSubst = kcvs
                 , seKvSubst = kvs } e
  = ContEx ids tcvs tvs kcvs kvs e

{- *********************************************************************
*                                                                      *
                        Let Floats
*                                                                      *
********************************************************************* -}

data LetFloats = LetFloats (OrdList OutBind) FloatFlag

type JoinFloat = OutBind
type JoinFloats = OrdList JoinFloat

data FloatFlag
  = FltStringLit -- single primitive string literal
  | FltOkSpec
  | FltCareful

instance Outputable LetFloats where
  ppr (LetFloats binds ff) = ppr ff $$ ppr (fromOL binds)

instance Outputable FloatFlag where
  ppr FltStringLit = text "FltStringLit"
  ppr FltOkSpec = text "FltOkSpec"
  ppr FltCareful = text "FltCareful"

andFF :: FloatFlag -> FloatFlag -> FloatFlag
andFF FltCareful _ = FltCareful
andFF FltOkSpec FltCareful = FltCareful
andFF FltOkSpec _ = FltOkSpec
andFF FltStringLit flt = flt

doFloatFromRhs :: FloatEnable -> TopLevelFlag -> RecFlag -> SimplFloats -> OutExpr -> Bool
doFloatFromRhs fe lvl is_rec SimplFloats{ sfLetFloats = LetFloats fs ff } rhs
  = floatEnabled lvl fe
    && not (isNilOL fs)
    && want_to_float
    && can_float
  where
    want_to_float = isTopLevel lvl || exprIsCheap rhs || exprIsExpandable rhs

    can_float = case ff of
      FltStringLit -> True
      FltOkSpec -> isNotTopLevel lvl && isNonRec is_rec
      FltCareful -> isNotTopLevel lvl && isNonRec is_rec

    floatEnabled :: TopLevelFlag -> FloatEnable -> Bool
    floatEnabled _ FloatDisabled = False
    floatEnabled lvl FloatNestedOnly = not (isTopLevel lvl)
    floatEnabled _ FloatEnabled = True

emptyLetFloats :: LetFloats
emptyLetFloats = LetFloats nilOL FltStringLit

isEmptyLetFloats :: LetFloats -> Bool
isEmptyLetFloats (LetFloats fs _) = isNilOL fs

emptyJoinFloats :: JoinFloats
emptyJoinFloats = nilOL

isEmptyJoinFloats :: JoinFloats -> Bool
isEmptyJoinFloats = isNilOL

unitLetFloat :: OutBind -> LetFloats
unitLetFloat bind = assert (all (not . isJoinId) (bindersOf bind)) $
  LetFloats (unitOL bind) (flag bind)
  where
    flag Rec{} = panic "what to do"
    flag (NonRec bndr rhs)
      | exprIsTickedString rhs = FltStringLit
      | exprOkForSpeculation rhs = FltOkSpec
      | otherwise = FltCareful

unitJoinFloat :: OutBind -> JoinFloats
unitJoinFloat bind = assert (all isJoinId (bindersOf bind)) $ unitOL bind

mkFloatBind :: SimplEnv -> OutBind -> (SimplFloats, SimplEnv)
mkFloatBind env bind = (floats, env { seInScope = in_scope' })
  where
    floats
      | isJoinBind bind
      = SimplFloats { sfLetFloats = emptyLetFloats
                    , sfJoinFloats = unitJoinFloat bind
                    , sfInScope = id_in_scope' }
      | otherwise
      = SimplFloats { sfLetFloats = unitLetFloat bind
                    , sfJoinFloats = emptyJoinFloats
                    , sfInScope = id_in_scope' }
    !in_scope'@(id_in_scope', _, _, _, _) = case seInScope env of
      (ids, tcvs, tvs, kcvs, kvs)
        -> (ids `extendInScopeSetBind` bind, tcvs, tvs, kcvs, kvs)

extendFloats :: SimplFloats -> OutBind -> SimplFloats 
extendFloats SimplFloats{ sfLetFloats = floats
                        , sfJoinFloats = jfloats
                        , sfInScope = in_scope } bind
  | isJoinBind bind
  = SimplFloats { sfInScope = in_scope'
                , sfLetFloats = floats
                , sfJoinFloats = jfloats' }
  | otherwise
  = SimplFloats { sfInScope = in_scope'
                , sfLetFloats = floats'
                , sfJoinFloats = jfloats }
  where
    in_scope' = in_scope `extendInScopeSetBind` bind
    floats' = floats `addLetFlts` unitLetFloat bind
    jfloats' = jfloats `addJoinFlts` unitJoinFloat bind  

addLetFloats :: SimplFloats -> LetFloats -> SimplFloats
addLetFloats floats let_floats
  = floats { sfLetFloats = sfLetFloats floats `addLetFlts` let_floats
           , sfInScope = sfInScope floats `extendInScopeFromLF` let_floats }

extendInScopeFromLF :: InScopeSet CoreId -> LetFloats -> InScopeSet CoreId
extendInScopeFromLF in_scope (LetFloats binds _)
  = foldlOL extendInScopeSetBind in_scope binds

addJoinFloats :: SimplFloats -> JoinFloats -> SimplFloats
addJoinFloats floats join_floats
  = floats { sfJoinFloats = sfJoinFloats floats `addJoinFlts` join_floats
           , sfInScope = foldlOL extendInScopeSetBind (sfInScope floats) join_floats }

addFloats :: SimplFloats -> SimplFloats -> SimplFloats
addFloats SimplFloats{ sfLetFloats = lf1, sfJoinFloats = jf1 }
          SimplFloats{ sfLetFloats = lf2, sfJoinFloats = jf2, sfInScope = in_scope }
  = SimplFloats { sfLetFloats = lf1 `addLetFlts` lf2
                , sfJoinFloats = jf1 `addJoinFlts` jf2
                , sfInScope = in_scope }

addLetFlts :: LetFloats -> LetFloats -> LetFloats
addLetFlts (LetFloats bs1 l1) (LetFloats bs2 l2)
  = LetFloats (bs1 `appOL` bs2) (l1 `andFF` l2)

letFloatBinds :: LetFloats -> [CoreBind]
letFloatBinds (LetFloats bs _) = fromOL bs

addJoinFlts :: JoinFloats -> JoinFloats -> JoinFloats
addJoinFlts = appOL

mkRecFloats :: SimplFloats -> SimplFloats
mkRecFloats floats@SimplFloats{ sfLetFloats = LetFloats bs _
                              , sfJoinFloats = jbs
                              , sfInScope = in_scope }
  = assertPpr (isNilOL bs || isNilOL jbs) (ppr floats) $
    SimplFloats { sfLetFloats = floats'
                , sfJoinFloats = jfloats'
                , sfInScope = in_scope }
  where
    !floats' | isNilOL bs = emptyLetFloats
             | otherwise = unitLetFloat (Rec (flattenBinds (fromOL bs)))
    !jfloats' | isNilOL jbs = emptyJoinFloats
              | otherwise = unitJoinFloat (Rec (flattenBinds (fromOL jbs)))

wrapFloats :: SimplFloats -> OutExpr -> OutExpr
wrapFloats floats@SimplFloats{ sfLetFloats = LetFloats bs flag
                             , sfJoinFloats = jbs
                             , sfInScope = in_scope } body
  = foldrOL mk_let (wrapJoinFloats jbs body) bs
  where mk_let | FltCareful <- flag = mkCoreLet
               | otherwise = Let

wrapJoinFloatsX :: SimplFloats -> OutExpr -> (SimplFloats, OutExpr)
wrapJoinFloatsX floats body
  = ( floats { sfJoinFloats = emptyJoinFloats }
    , wrapJoinFloats (sfJoinFloats floats) body )

wrapJoinFloats :: JoinFloats -> OutExpr -> OutExpr
wrapJoinFloats join_floats body = foldrOL Let body join_floats

getTopFloatBinds :: SimplFloats -> [CoreBind]
getTopFloatBinds SimplFloats{ sfLetFloats = lbs, sfJoinFloats = jbs }
  = assert (isNilOL jbs) $ letFloatBinds lbs

{-# INLINE mapLetFloats #-}
mapLetFloats :: LetFloats -> ((CoreId, CoreExpr) -> (CoreId, CoreExpr)) -> LetFloats
mapLetFloats (LetFloats fs ff) fun
  = LetFloats fs1 ff
  where
    app (NonRec b e) = case fun (b, e) of (b', e') -> NonRec b' e'
    app (Rec bs) = Rec (strictMap fun bs)
    !fs1 = mapOL' app fs

{- *********************************************************************
*                                                                      *
        Substitution of Vars
*                                                                      *
********************************************************************* -}

substId :: SimplEnv -> InId -> SimplSR
substId SimplEnv{ seInScope = in_scope, seIdSubst = ids } v
  = case lookupVarEnv ids v of
      Nothing -> DoneId (refineFromInScope in_scope v)
      Just (DoneId v) -> DoneId (refineFromInScope in_scope v)
      Just res -> res

refineFromInScope :: TermSubstInScope -> CoreId -> CoreId
refineFromInScope (in_scope, _, _, _, _) v
  | isLocalId v = case lookupInScope in_scope v of
                    Just v' -> v'
                    Nothing -> pprPanic "refinedFromInScope" (ppr in_scope $$ ppr v)
  | otherwise = v

lookupRecBndr :: SimplEnv -> InId -> OutId
lookupRecBndr SimplEnv{ seInScope = in_scope, seIdSubst = ids } v
  = case lookupVarEnv ids v of
      Just (DoneId v) -> v
      Just _ -> pprPanic "lookupRecBndr" (ppr v)
      Nothing -> refineFromInScope in_scope v

{- *********************************************************************
*                                                                      *
                Substituting an Id binder
*                                                                      *
********************************************************************* -}

simplBinders :: SimplEnv -> [(InBndr, a)] -> SimplM (SimplEnv, [(OutBndr, a)])
simplBinders !env bndrs = mapAccumLM simplBinder env bndrs

simplIdBinders :: SimplEnv -> [InId] -> SimplM (SimplEnv, [OutId])
simplIdBinders !env bndrs = mapAccumLM simplIdBinder env bndrs

-- TODO: I may have to substitute into the kind as well. (Change 'a' to 'Maybe CoreMonoKind')
simplBinder :: SimplEnv -> (InBndr, a) -> SimplM (SimplEnv, (OutBndr, a))
simplBinder !env (var, a) = case var of
  C.Id bndr -> do let (env', id) = substIdBndr env bndr
                  seqId id `seq` return (env', (C.Id id, a))
  Tv bndr -> do let (env', tv) = substTyVarBndr env bndr
                seqVar tv `seq` return (env', (Tv tv, a))
  KCv bndr -> do let (env', kcv) = substKiCoVarBndr env bndr
                 seqVar kcv `seq` return (env', (KCv kcv, a))
  Kv bndr -> do let (env', kv) = substKiVarBndr env bndr
                seqVar kv `seq` return (env', (Kv kv, a))  

simplIdBinder :: SimplEnv -> InId -> SimplM (SimplEnv, OutId)
simplIdBinder !env bndr
  = let (env', id) = substIdBndr env bndr
    in seqId id `seq` return (env', id)

simplNonRecBndr :: SimplEnv -> InId -> SimplM (SimplEnv, OutId)
simplNonRecBndr !env id = do
  let (!env1, id1) = substIdBndr env id
  seqId id1 `seq` return (env1, id1)

simplRecBndrs :: SimplEnv -> [InId] -> SimplM SimplEnv
simplRecBndrs env ids
  = assert (all (not . isJoinId) ids) $ do
  let (!env1, ids1) = mapAccumL substIdBndr env ids
  seqIds ids1 `seq` return env1

substIdBndr :: SimplEnv -> InId -> (SimplEnv, OutId)
substIdBndr env id = subst_id_bndr env id (\x -> x)

{-# INLINE subst_id_bndr #-}
subst_id_bndr
  :: SimplEnv
  -> InId
  -> (OutId -> OutId)
  -> (SimplEnv, OutId)
subst_id_bndr env@SimplEnv{ seInScope = (in_scope, tcvs, tvs, kcvs, kvs)
                          , seIdSubst = id_subst } old_id adjust_type
  = ( env { seInScope = (new_in_scope, tcvs, tvs, kcvs, kvs)
          , seIdSubst = new_subst }
    , new_id )
  where
    !id1 = uniqAway in_scope old_id
    !id2 = substIdType env id1
    !id3 = zapFragileIdInfo id2

    !new_id = adjust_type id3

    !new_subst
      | new_id /= old_id
      = extendVarEnv id_subst old_id (DoneId new_id)
      | otherwise
      = delVarEnv id_subst old_id

    !new_in_scope = in_scope `extendInScopeSet` new_id

seqId :: CoreId -> ()
seqId id = seqType (varType id) `seq`
           idInfo id `seq`
           ()

seqIds :: [CoreId] -> ()
seqIds [] = ()
seqIds (id:ids) = seqId id `seq` seqIds ids

seqVar :: a -> ()
seqVar b = b `seq` ()

{- *********************************************************************
*                                                                      *
                Join points
*                                                                      *
********************************************************************* -}

simplNonRecJoinBndr
  :: SimplEnv
  -> InId
  -> OutType
  -> SimplM (SimplEnv, OutId)
simplNonRecJoinBndr env id res_ty = do
  let (env1, id1) = simplJoinBndr res_ty env id
  seqId id1 `seq` return (env1, id1)

simplRecJoinBndrs
  :: SimplEnv
  -> [InId]
  -> OutType
  -> SimplM SimplEnv
simplRecJoinBndrs env ids res_ty
  = assert (all isJoinId ids) $ do
      let (env1, ids1) = mapAccumL (simplJoinBndr res_ty) env ids
      seqIds ids1 `seq` return env1

simplJoinBndr :: OutType -> SimplEnv -> InId -> (SimplEnv, OutId)
simplJoinBndr res_ty env id
  = subst_id_bndr env id (adjustJoinPointType res_ty)

adjustJoinPointType :: CoreType -> CoreId -> CoreId
adjustJoinPointType new_res_ty join_id = panic "adjustJoinPointType"
  -- = assert (isJoinId join_id) $
  --   setVarType join_id new_join_ty
  -- where
  --   join_arity = isJoinArity join_id
  --   orig_ty = varType join_id

  --   new_join_ty = go join_arity orig_ty

  --   go :: JoinArity -> CoreType -> CoreType
  --   go n ty
  --     | n == 0
  --     = new_res_ty

  --     | Just (arg_bndr, body_ty) <- splitPiTy_maybe ty
  --     = let body_ty' = go (n - 1) body_ty
  --       in case arg_bndr of
  --            NamedTy b -> mkForAllTy b body_ty'
  --            NamedKiCo b -> mkForAllKiCo b body_ty'
  --            NamedKi b -> mkBigLamTy b body_ty'
  --            AnonTy arg_ty -> mkFunTy fun_kind arg_ty body_ty'




{- *********************************************************************
*                                                                      *
                Impedance matching to type substitution
*                                                                      *
********************************************************************* -}

getSubst :: SimplEnv -> CoreSubst
getSubst SimplEnv{ seInScope = in_scope
                 , seTCvSubst = tcvs
                 , seTvSubst = tvs
                 , seKCvSubst = kcvs
                 , seKvSubst = kvs }
  = mkCoreSubst in_scope emptyVarEnv tcvs tvs kcvs kvs

substTy :: HasDebugCallStack => SimplEnv -> CoreType -> CoreType
substTy env ty = Subst.substTy (getSubst env) ty

substKiCo :: HasDebugCallStack => SimplEnv -> CoreKindCoercion -> CoreKindCoercion
substKiCo env co = Subst.substKiCo (getSubst env) co

substTyCo :: HasDebugCallStack => SimplEnv -> CoreTypeCoercion -> CoreTypeCoercion
substTyCo env co = panic "Subst.substTyCo (getSubst env) co"

substMonoKi :: HasDebugCallStack => SimplEnv -> CoreMonoKind -> CoreMonoKind
substMonoKi env ki = Subst.substMonoKi (getSubst env) ki

substTyVarBndr :: SimplEnv -> CoreTyVar -> (SimplEnv, CoreTyVar)
substTyVarBndr env tv
  = case Subst.substTyVarBndr (getSubst env) tv of
      (subst, tv') -> ( env { seInScope = termSubstInScope subst
                           , seTCvSubst = tcv_env subst
                           , seTvSubst = tv_env subst
                           , seKCvSubst = kcv_env subst
                           , seKvSubst = kv_env subst }
                     , tv' )

substKiCoVarBndr :: SimplEnv -> CoreKiCoVar -> (SimplEnv, CoreKiCoVar)
substKiCoVarBndr env cv
  = case Subst.substKiCoVarBndr (getSubst env) cv of
      (subst, cv') -> ( env { seInScope = termSubstInScope subst
                            , seKCvSubst = kcv_env subst
                            , seKvSubst = kv_env subst }
                      , cv' )

substKiVarBndr :: SimplEnv -> CoreKiVar -> (SimplEnv, CoreKiVar)
substKiVarBndr env kv
  = case Subst.substKiVarBndr (getSubst env) kv of
      (subst, kv') -> ( env { seInScope = termSubstInScope subst
                            , seKvSubst = kv_env subst }
                      , kv' )

substIdType :: SimplEnv -> CoreId -> CoreId
substIdType SimplEnv{ seInScope = in_scope
                    , seTvSubst = tv_env
                    , seKCvSubst = kcv_env
                    , seKvSubst = kv_env } id
  | (isEmptyVarEnv tv_env && isEmptyVarEnv kcv_env && isEmptyVarEnv kv_env)
    || no_free_vars
  = id
  | otherwise
  = updateVarType (substTyUnchecked subst) id
  where
    no_free_vars = noFreeVarsOfType old_ty
    subst = mkCoreSubst in_scope emptyVarEnv emptyVarEnv tv_env kcv_env kv_env
    old_ty = varType id
