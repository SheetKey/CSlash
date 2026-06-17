module CSlash.Core.Opt.Exitify (exitifyProgram) where

import CSlash.Builtin.Uniques
import CSlash.Core as C
import CSlash.Core.Make
import CSlash.Core.Utils
import CSlash.Core.FVs
import CSlash.Core.Type
import CSlash.Core.Kind

import CSlash.Types.Var
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Types.Basic( JoinPointHood(..), JoinArity )

import CSlash.Utils.Monad.State.Strict
import CSlash.Utils.Misc( mapSnd )
import Data.Maybe (mapMaybe)

import CSlash.Data.FastString

import Data.Bifunctor
import Control.Monad

exitifyProgram :: CoreProgram -> CoreProgram
exitifyProgram binds = map goTopLvl binds
  where
    goTopLvl (NonRec v e) = NonRec v (go in_scope_toplvl e)
    goTopLvl (Rec pairs) = Rec (map (second (go in_scope_toplvl)) pairs)

    in_scope_toplvl = emptyInScopeSet `extendInScopeSetBndrs` binds

    go :: InScopeSet CoreId -> CoreExpr -> CoreExpr
    go _ e@Var{} = e
    go _ e@Lit{} = e
    go _ e@Type{} = e
    go _ e@KiCo{} = e
    go _ e@Kind{} = e
    go in_scope (Cast e' c) = Cast (go in_scope e') c
    go in_scope (Tick t e') = Tick t (go in_scope e')
    go in_scope (App e1 e2) = App (go in_scope e1) (go in_scope e2)

    go in_scope (Lam (C.Id v) k e') = Lam (C.Id v) k (go in_scope' e')
      where in_scope' = in_scope `extendInScopeSet` v
    go in_scope (Lam v k e') = Lam v k (go in_scope e')

    go in_scope (Case scrut bndr ty alts)
      = Case (go in_scope scrut) bndr ty (map go_alt alts)
      where
        in_scope1 = in_scope `extendInScopeSet` bndr
        go_alt (Alt dc pats rhs) = Alt dc pats (go in_scope' rhs)
          where
            in_scope' = in_scope1 `extendInScopeSetList` pats

    go in_scope (Let (NonRec bndr rhs) body)
      = Let (NonRec bndr (go in_scope rhs)) (go in_scope' body)
      where in_scope' = in_scope `extendInScopeSet` bndr

    go in_scope (Let (Rec pairs) body)
      | is_join_rec = mkCoreLets (exitifyRec in_scope' pairs') body'
      | otherwise = Let (Rec pairs') body'
      where
        is_join_rec = any (isJoinId . fst) pairs
        in_scope' = in_scope `extendIdInScopeSetBind` (Rec pairs)
        pairs' = mapSnd (go in_scope') pairs
        body' = go in_scope' body

type ExitifyM = State [(JoinId, CoreExpr)]

exitifyRec :: InScopeSet CoreId -> [(CoreId, CoreExpr)] -> [CoreBind]
exitifyRec in_scope pairs = [NonRec xid rhs | (xid, rhs) <- exits] ++ [Rec pairs']
  where
    ann_pairs = map (second freeVars) pairs

    recursive_calls = mkVarSet $ map fst pairs

    (pairs', exits) = (`runState` []) $
      forM ann_pairs $ \(x, rhs) -> do
        let (args, body) = collectNAnnBndrs (idJoinArity x) rhs
        body' <- go args body
        let rhs' = mkCoreLams args body'
        return (x, rhs')

    go :: [(CoreBndr, Maybe CoreMonoKind)] -> CoreExprWithFVs -> ExitifyM CoreExpr
    go captured ann_e
      | let fvs@(id_fvs, _, _, _, _) = dVarSetsToVarSets (freeVarsOf ann_e)
      , disjointVarSet id_fvs recursive_calls
      = go_exit captured (deAnnotate ann_e) fvs

    go captured (_, AnnCase scrut bndr ty alts) = do
      alts' <- forM alts $ \(AnnAlt dc pats rhs) -> do
        rhs' <- go (captured ++ ids_to_bndrs (bndr : pats)) rhs
        return (Alt dc pats rhs')
      return $ Case (deAnnotate scrut) bndr ty alts'

    go captured (_, AnnLet ann_bind body)
      | AnnNonRec j rhs <- ann_bind
      , JoinPoint join_arity <- idJoinPointHood j
      = do let (params, join_body) = collectNAnnBndrs join_arity rhs
           join_body' <- go (captured ++ params) join_body
           let rhs' = mkCoreLams params join_body'
           body' <- go (captured ++ [id_to_bndr j]) body
           return $ Let (NonRec j rhs') body'

      | AnnRec pairs <- ann_bind
      , isJoinId (fst (head pairs))
      = do let js = map fst pairs
           pairs' <- forM pairs $ \(j, rhs) -> do
             let join_arity = idJoinArity j
                 (params, join_body) = collectNAnnBndrs join_arity rhs
             join_body' <- go (captured ++ ids_to_bndrs js ++ params)
                           join_body
             let rhs' = mkCoreLams params join_body'
             return (j, rhs')
           body' <- go (captured ++ ids_to_bndrs js) body
           return $ Let (Rec pairs') body'

      | otherwise
      = do body' <- go (captured ++ ids_to_bndrs (bindersOf bind)) body
           return $ Let bind body'
      where
        bind = deAnnBind ann_bind

    go _ ann_e = return (deAnnotate ann_e)

    go_exit :: [(CoreBndr, Maybe CoreMonoKind)] -> CoreExpr -> CoreVarSets -> ExitifyM CoreExpr

    go_exit captured e fvs@(id_fvs, _, _, _, _)
      | (Var f, args) <- collectArgs e
      , isJoinId f
      , all isCapturedVarArg args
      = return e

      | not is_interesting
      = return e

      | captures_join_points
      = return e

      | otherwise
      = do let rhs = mkCoreLams abs_vars e
               avoid = in_scope `extendInScopeSetList` id_bndrs captured
           v <- addExit avoid (length abs_vars) rhs
           return $ mkBndrApps (Var v) (fst <$> abs_vars)

      where
        isCapturedVarArg (Var v) = v `elem` id_bndrs captured
        isCapturedVarArg _ = False

        is_interesting = anyVarSet isLocalId $ id_fvs `minusVarSet` mkVarSet (id_bndrs captured)

        abs_vars :: [(CoreBndr, Maybe CoreMonoKind)]
        abs_vars = snd $ foldr pick (fvs, []) captured
          where
            pick
              :: (CoreBndr, Maybe CoreMonoKind)
              -> (CoreVarSets, [(CoreBndr, Maybe CoreMonoKind)])
              -> (CoreVarSets, [(CoreBndr, Maybe CoreMonoKind)])
            pick (v, k) (fvs', acc)
              | v `bndrElemCoreVarSets` fvs'
              = (fvs' `delBndrCoreVarSets` v, (zap v, k) : acc)
              | otherwise = (fvs', acc)

        zap (C.Id v) = C.Id $ setIdInfo v vanillaIdInfo
        zap v = v

        captures_join_points = any (isJoinIdBndr . fst) abs_vars

mkExitJoinId :: InScopeSet CoreId -> CoreType -> JoinArity -> ExitifyM JoinId
mkExitJoinId in_scope ty join_arity = do
  fs <- get
  let avoid = in_scope `extendInScopeSetList` (map fst fs)
                       `extendInScopeSet` exit_id_tmpl
  return (uniqAway avoid exit_id_tmpl)
  where
    exit_id_tmpl = mkSysLocal (fsLit "exit") initExitJoinUnique ty
                   `asJoinId` join_arity

addExit :: InScopeSet CoreId -> JoinArity -> CoreExpr -> ExitifyM JoinId
addExit in_scope join_arity rhs = do
  let ty = exprType rhs
  v <- mkExitJoinId in_scope ty join_arity
  fs <- get
  pure ((v, rhs):fs)
  return v

-- TODO check kis
id_to_bndr :: CoreId -> (CoreBndr, Maybe CoreMonoKind)
id_to_bndr id = (C.Id id, Just (BIKi UKd))
 
ids_to_bndrs :: [CoreId] -> [(CoreBndr, Maybe CoreMonoKind)]
ids_to_bndrs = fmap id_to_bndr

id_bndrs :: [(CoreBndr, Maybe CoreMonoKind)] -> [CoreId]
id_bndrs = mapMaybe id_bndr_maybe

id_bndr_maybe :: (CoreBndr, Maybe CoreMonoKind) -> Maybe CoreId
id_bndr_maybe (C.Id id, _) = Just id
id_bndr_maybe _ = Nothing
