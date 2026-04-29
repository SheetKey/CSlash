{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Opt.Simplify.Env where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Core.Opt.Coercion ( OptCoercionOpts )
import CSlash.Core.Opt.Simplify.Monad
import CSlash.Core
import CSlash.Core.Utils
import CSlash.Core.Unfold
import CSlash.Core.Subst as Subst
import CSlash.Core.Kind
import CSlash.Core.Make ( mkWildValBinder{-, mkCoreLet-} )
import CSlash.Core.Type
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

emptyLetFloats :: LetFloats
emptyLetFloats = LetFloats nilOL FltStringLit

isEmptyLetFloats :: LetFloats -> Bool
isEmptyLetFloats (LetFloats fs _) = isNilOL fs

emptyJoinFloats :: JoinFloats
emptyJoinFloats = nilOL

isEmptyJoinFloats :: JoinFloats -> Bool
isEmptyJoinFloats = isNilOL

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
