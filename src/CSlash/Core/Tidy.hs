module CSlash.Core.Tidy where

import CSlash.Core as C
import CSlash.Core.Type
import CSlash.Core.Type.Tidy

import CSlash.Core.Seq ( seqUnfolding )
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.Demand ( zapDmdEnvSig, isStrUsedDmd )
-- import GHC.Core.Coercion ( tidyCo )
import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Unique (getUnique)
import CSlash.Types.Unique.FM
import CSlash.Types.Name hiding (tidyNameOcc, varName)
import CSlash.Types.Name.Set
import CSlash.Types.SrcLoc
import CSlash.Types.Tickish
import CSlash.Data.Maybe
import CSlash.Utils.Misc
import Data.List (mapAccumL)
import CSlash.Utils.Outputable
-- import GHC.Types.RepType (typePrimRep)
import CSlash.Utils.Panic
-- import GHC.Types.Basic (isMarkedCbv, CbvMark (..))
-- import GHC.Core.Utils (shouldUseCbvForId)

{- *********************************************************************
*                                                                      *
            Tidying expressions, rules
*                                                                      *
********************************************************************* -}

tidyBind :: CoreTidyEnv -> CoreBind -> (CoreTidyEnv, CoreBind)
tidyBind env (NonRec bndr rhs) =
  let (env', bndr') = tidyLetBndr env env bndr
      tidy_rhs = tidyExpr env' rhs
  in (env', NonRec bndr' tidy_rhs)
  
tidyBind env (Rec prs) =
  let (bndrs, rhss) = unzip prs
      (env', bndrs') = mapAccumL (tidyLetBndr env') env bndrs
  in map (tidyExpr env') rhss =: \rhss' -> (env', Rec (zip bndrs' rhss'))

tidyExpr :: CoreTidyEnv -> CoreExpr -> CoreExpr
tidyExpr env (Var v) = Var (tidyVarOcc env v)
tidyExpr env (Type ty) = Type (tidyType (toTypeEnv env) ty)
tidyExpr env (KiCo co) = panic "tidy KiCo"
tidyExpr env (Kind ki) = Kind (tidyMonoKind (toTypeEnv env) ki)
tidyExpr _ (Lit lit) = Lit lit
tidyExpr env (App f a) = App (tidyExpr env f) (tidyExpr env a)
tidyExpr env (Tick t e) = Tick (tidyTickish env t) (tidyExpr env e)
tidyExpr env (Cast e co) = Cast (tidyExpr env e) (panic "tidy TyCo")

tidyExpr env (Let b e)
  = tidyBind env b =: \(env', b') -> Let b' (tidyExpr env' e)

tidyExpr env (Case e b ty alts)
  = tidyBndr env b =: \(env', b) ->
    Case (tidyExpr env e) b (tidyType (toTypeEnv env) ty) (map (tidyAlt env') alts)

tidyExpr env (Lam b k e)
  = tidyLamBndr env b =: \(env', b) ->
    Lam b (tidyMonoKind (toTypeEnv env) <$> k) (tidyExpr env' e)

tidyAlt :: CoreTidyEnv -> CoreAlt -> CoreAlt
tidyAlt env (Alt con vs rhs)
  = tidyBndrs env vs =: \(env', vs) ->
    Alt con vs (tidyExpr env' rhs)

tidyTickish :: CoreTidyEnv -> CoreTickish -> CoreTickish
tidyTickish _ other@CpcTick{} = other

tidyRules :: CoreTidyEnv -> [CoreRule] -> [CoreRule]
tidyRules _ [] = []
tidyRules env (rule : rules)
  = tidyRule env rule =: \rule ->
    tidyRules env rules =: \rules ->
    (rule : rules)

tidyRule :: CoreTidyEnv -> CoreRule -> CoreRule
tidyRule _ rule@BuiltinRule{} = rule
tidyRule env rule@Rule{ ru_bndrs = bndrs, ru_args = args
                      , ru_rhs = rhs, ru_fn = fn, ru_rough = mb_ns }
  = tidyLamBndrs env bndrs =: \(env', bndrs) ->
    map (tidyExpr env') args =: \args ->
    rule { ru_bndrs = bndrs
         , ru_args = args
         , ru_rhs = tidyExpr env' rhs
         , ru_fn = tidyNameOcc env fn
         , ru_rough = map (fmap (tidyNameOcc env')) mb_ns }

{- *********************************************************************
*                                                                      *
               Tidying non-top-level binders
*                                                                      *
********************************************************************* -}

-- Only used for rules
tidyNameOcc :: CoreTidyEnv -> Name -> Name
tidyNameOcc (_, var_env, _, _, _, _) n = case lookupUFM_Directly var_env (getUnique n) of
  Just v -> varName v
  Nothing -> n

tidyVarOcc :: CoreTidyEnv -> CoreId -> CoreId
tidyVarOcc (_, var_env, _, _, _, _) v = lookupVarEnv var_env v `orElse` v

tidyBndr :: CoreTidyEnv -> CoreId -> (CoreTidyEnv, CoreId)
tidyBndr env var = tidyIdBndr env var

tidyBndrs :: CoreTidyEnv -> [CoreId] -> (CoreTidyEnv, [CoreId])
tidyBndrs env vars = mapAccumL tidyBndr env vars

-- Used for rules (which is why it doesn't take the function kinds)
tidyLamBndrs :: CoreTidyEnv -> [CoreBndr] -> (CoreTidyEnv, [CoreBndr])
tidyLamBndrs env vars = mapAccumL tidyLamBndr env vars

tidyLamBndr :: CoreTidyEnv -> CoreBndr -> (CoreTidyEnv, CoreBndr)
tidyLamBndr env var = case var of
  C.Id var -> C.Id `onSnd` tidyIdBndr env var
  Tv var -> Tv `onSnd` withTypeBndr env (flip tidyTyVarBndr var)
  KCv var -> KCv `onSnd` withTypeBndr env (flip tidyKiCoVarBndr var)
  Kv var -> Kv `onSnd` withTypeBndr env (flip tidyKiVarBndr var)

tidyIdBndr :: CoreTidyEnv -> CoreId -> (CoreTidyEnv, CoreId)
tidyIdBndr env@(tidy_env, var_env, tcv, tv, kcv, kv) id
  = case tidyOccName tidy_env (getOccName id) of
      (tidy_env', occ') ->
        let ty' = tidyType (toTypeEnv env) (varType id)
            name' = mkInternalName (varUnique id) occ' noSrcSpan
            id' = mkLocalIdWithInfo name' ty' new_info
            var_env' = extendVarEnv var_env id id'

            new_info = vanillaIdInfo
                       `setOccInfo` occInfo old_info
                       `setUnfoldingInfo` new_unf
                       `setOneShotInfo` oneShotInfo old_info

            old_info = idInfo id
            old_unf = realUnfoldingInfo old_info
            new_unf = trimUnfolding old_unf
        in ((tidy_env', var_env', tcv, tv, kcv, kv), id')

tidyLetBndr :: CoreTidyEnv -> CoreTidyEnv -> CoreId -> (CoreTidyEnv, CoreId)
tidyLetBndr rec_tidy_env env@(tidy_env, var_env, tcv, tv, kcv, kv) id
  = case tidyOccName tidy_env (getOccName id) of
      (tidy_env', occ') ->
        let ty' = tidyType (toTypeEnv env) (varType id)
            name' = mkInternalName (varUnique id) occ' noSrcSpan
            details = idDetails id
            id' = mkLocalIdWithDetailsAndInfo details name' ty' new_info
            var_env' = extendVarEnv var_env id id'

            old_info = idInfo id
            new_info = vanillaIdInfo
                       `setOccInfo` occInfo old_info
                       `setArityInfo` arityInfo old_info
                       `setDmdSigInfo` zapDmdEnvSig (dmdSigInfo old_info)
                       `setDemandInfo` demandInfo old_info
                       `setInlinePragInfo` inlinePragInfo old_info
                       `setUnfoldingInfo` new_unf

            old_unf = realUnfoldingInfo old_info
            new_unf = tidyNestedUnfolding rec_tidy_env old_unf
        in ((tidy_env', var_env', tcv, tv, kcv, kv), id')

tidyNestedUnfolding :: CoreTidyEnv -> Unfolding -> Unfolding
tidyNestedUnfolding _ NoUnfolding = NoUnfolding
tidyNestedUnfolding _ OtherCon{} = evaldUnfolding
tidyNestedUnfolding tidy_env unf@CoreUnfolding{ uf_tmpl = unf_rhs, uf_src = src, uf_cache = cache }
  | isStableSource src
  = seqIt $ unf { uf_tmpl = tidyExpr tidy_env unf_rhs }
  | uf_is_value cache
  = evaldUnfolding
  | otherwise
  = noUnfolding
  where
    seqIt unf = seqUnfolding unf `seq` unf

(=:) :: a -> (a -> b) -> b
m =: k = m `seq` k m

onSnd :: (b -> c) -> (a, b) -> (a, c)
onSnd f (a, b) = (a, f b)
