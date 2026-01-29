{-# LANGUAGE BangPatterns #-}

module CSlash.Tc.Utils.Instantiate where

import {-# SOURCE #-} CSlash.Tc.Utils.Unify (unifyKind)

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
import CSlash.Core.Type.Ppr
import CSlash.Core.Type.FVs
import CSlash.Core.Subst
import CSlash.Core.Kind
-- import CSlash.Core.TyCo.Ppr ( debugPprType )
-- import GHC.Core.Class( Class )
import CSlash.Core.DataCon
-- import GHC.Core.Coercion.Axiom

-- import {-# SOURCE #-}   GHC.Tc.Gen.Expr( tcCheckPolyExpr, tcSyntaxOp )
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
import CSlash.Types.Basic ( TypeOrKind(..), Arity, VisArity )
import CSlash.Types.Error
import CSlash.Types.SourceText
import CSlash.Types.SrcLoc as SrcLoc
import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Var.Id
import CSlash.Types.Name hiding (varName)
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
            Instantiation and skolemization
*                                                                      *
********************************************************************* -}

topSkolemize
  :: SkolemInfo
  -> SkolemInfo
  -> SigmaType Tc
  -> TcM (CsWrapper Tc, [(Name, TcKiVar)], [(Name, TcTyVar)], RhoType Tc)
topSkolemize skolem_info_ki skolem_info ty = go init_subst idCsWrapper [] [] ty
  where
    init_subst = mkEmptySubst $ mkInScopeSets $ varsOfType ty

    go subst wrap kv_prs tv_prs ty
      | (kvs, tvs, inner_ty) <- tcSplitSigma ty
      , not (null kvs && null tvs)
      = do (subst', tckvs1, tctvs1)
             <- tcInstSkolTyKiVarsX skolem_info_ki skolem_info subst kvs tvs
           let kvs1 = TcKiVar <$> tckvs1
               tvs1 = TcTyVar <$> tctvs1
           traceTc "topSkol"
             $ vcat [ ppr kvs <+> vcat (map (ppr . getSrcSpan) kvs)
                    , ppr kvs1 <+> vcat (map (ppr . getSrcSpan) kvs1)
                    , ppr tvs <+> vcat (map (ppr . getSrcSpan) tvs)
                    , ppr tvs1 <+> vcat (map (ppr . getSrcSpan) tvs1) ]
           go subst' (wrap <.> mkWpKiLams kvs1 <.> mkWpTyLams tvs1)
                     (kv_prs ++ (map varName kvs `zip` tckvs1))
                     (tv_prs ++ (map varName tvs `zip` tctvs1))
                     inner_ty
      | otherwise
      = do traceTc "topSkol done" empty
           return (wrap, kv_prs, tv_prs, substTy subst ty)

skolemizeRequired
  :: SkolemInfo
  -> VisArity
  -> SigmaType Tc
  -> TcM (VisArity, CsWrapper Tc, [Name], [ForAllBinder TcTyVar], RhoType Tc)
skolemizeRequired skolem_info n_req sigma
  = go n_req init_subst idCsWrapper [] [] sigma
  where
    init_subst = mkEmptySubst $ mkInScopeSets $ varsOfType sigma

    go n_req subst wrap acc_nms acc_bndrs ty
      | (n_req', bndrs, inner_ty) <- tcSplitForAllTyVarsReqTVBindersN n_req ty
      , not (null bndrs)
      = do (subst', bndrs1) <- tcInstSkolTyVarBndrsX skolem_info subst bndrs
           let tvs1 = TcTyVar <$> binderVars bndrs1
           traceTc "skolemizeRequired, not fixing tv vis in wrapper" empty
           go n_req' subst'
             (wrap <.> mkWpTyLams tvs1)
             (acc_nms ++ map (varName . binderVar) bndrs)
             (acc_bndrs ++ bndrs1)
             inner_ty
      | otherwise
      = return (n_req, wrap, acc_nms, acc_bndrs, substTy subst ty)

topInstantiate :: CtOrigin -> SigmaType Tc -> TcM (CsWrapper Tc, RhoType Tc)
topInstantiate orig sigma
  | (kvs, body1) <- tcSplitBigLamKiVars sigma
  , (tvs, body2) <- tcSplitForAllInvisTyVars body1
  , not (null kvs && null tvs)
  = do (_, _, wrap1, body3) <- instantiateSigma orig kvs tvs body2 sigma
       (wrap2, body4) <- topInstantiate orig body3
       return (wrap2 <.> wrap1, body4)
  | otherwise
  = return (idCsWrapper, sigma)

-- TODO: Some of the 'tvs' are actually kicovars!
-- For now we deal with that here.
-- In the future (when tyvars and kicovars are distinct types),
-- this must accept a 'tvs' arg and a 'kcvs' arg.
instantiateSigma
  :: CtOrigin
  -> [KiVar Tc]
  -> [TyVar Tc]
  -> SigmaType Tc
  -> SigmaType Tc-- the type before splitting of kvs and tvs (for finding in_scope)
  -> TcM ([TcKiVar], [TcTyVar], CsWrapper Tc, SigmaType Tc)
instantiateSigma orig kvs tvs body_ty orig_type = do
  (subst1, inst_kvs) <- mapAccumLM newMetaKiVarX empty_subst kvs
  -- let inst_preds = substMonoKis kv_subst preds
  -- kcos <- instCallKiConstraints orig inst_preds
  -- let tv_subst1 = extendTvSubstList (mk_empty_tv_subst kv_subst)  kcvs (KindCoercion <$> kcos)
  (subst, inst_tvs) <- mapAccumLM newMetaTyVarX subst1 tvs
  traceTc "instantiateSigma" (ppr subst)
  let inst_body = substTy subst body_ty
      inst_kv_kis = mkKiVarKis $ TcKiVar <$> inst_kvs
      inst_tv_tys = mkTyVarTys $ TcTyVar <$> inst_tvs
  -- let wrap = mkWpTyApps inst_tv_tys <.> mkWpKiCoApps kcos <.> mkWpKiApps inst_kv_kis
  let wrap =mkWpTyApps inst_tv_tys <.> mkWpKiApps inst_kv_kis
  traceTc "Instantiating"
    $ vcat [ text "origin" <+> pprCtOrigin orig
           , text "kvs" <+> ppr kvs
           -- , text "kcvs" <+> ppr kcvs
           , text "tvs" <+> ppr tvs
           , text "type" <+> debugPprType body_ty
           , text "orig_type" <+> debugPprType orig_type
           , text "with" <+> vcat (map debugPprMonoKind inst_kv_kis
                                   -- ++ map ppr kcos
                                   ++ map debugPprType inst_tv_tys) ]
  return (inst_kvs, inst_tvs, wrap, inst_body)
  where
    empty_subst = mkEmptySubst $ mkInScopeSets $ varsOfType orig_type

{- *********************************************************************
*                                                                      *
            Instantiating a call
*                                                                      *
********************************************************************* -}

instCallKiConstraints :: CtOrigin -> [PredKind Tc] -> TcM [KindCoercion Tc]
instCallKiConstraints orig preds
  | null preds
  = return []
  | otherwise
  = do kcos <- mapM go preds
       traceTc "instCallKiConstraints" (ppr kcos)
       return kcos
  where
    go :: PredKind Tc -> TcM (KindCoercion Tc)
    go pred
      | KiPredApp kc k1 k2 <- pred
      = unifyKind Nothing kc k1 k2
      | otherwise
      = panic "instCallKiConstraints"

{- *********************************************************************
*                                                                      *
         Instantiating Kinds
*                                                                      *
********************************************************************* -}

tcInstInvisibleKiBinder :: Subst p Tc -> KiVar p -> TcM (Subst p Tc, Type Tc)
tcInstInvisibleKiBinder subst kv = do
  (subst', kv') <- newMetaKiVarX subst kv
  return (subst', Embed $ mkKiVarKi $ TcKiVar kv')

{- *********************************************************************
*                                                                      *
        SkolemTvs/Kvs (immutable)
*                                                                      *
********************************************************************* -}

tcInstSkolTyKiVarsX
  :: SkolemInfo
  -> SkolemInfo
  -> Subst Tc Tc
  -> [KiVar Tc] -> [TyVar Tc]
  -> TcM (Subst Tc Tc, [TcKiVar], [TcTyVar])
tcInstSkolTyKiVarsX = tcInstSkolTyKiVarsPushLevel

tcInstSkolTyVarsX
  :: SkolemInfo -> Subst Tc Tc -> [TyVar Tc] -> TcM (Subst Tc Tc, [TcTyVar])
tcInstSkolTyVarsX skol_info subs vars = do
  (subst', kivars, tyvars) <- tcInstSkolTyKiVarsX skol_info skol_info subs [] vars
  massert (null kivars)
  pure (subst', tyvars)

tcInstSkolTyVarBndrsX
  :: SkolemInfo
  -> Subst Tc Tc
  -> [ForAllBinder (TyVar Tc)]
  -> TcM (Subst Tc Tc, [ForAllBinder TcTyVar])
tcInstSkolTyVarBndrsX skol_info subs bndrs = do
  (subst', kibndrs, bndrs') <- tcInstSkolTyKiVarsX skol_info skol_info subs [] (binderVars bndrs)
  massert (null kibndrs)
  pure (subst', zipWith Bndr bndrs' flags)
  where
    flags = binderFlags bndrs
  
tcInstSkolTyKiVarsPushLevel
  :: SkolemInfo
  -> SkolemInfo
  -> Subst Tc Tc
  -> [KiVar Tc] -> [TyVar Tc]
  -> TcM (Subst Tc Tc, [TcKiVar], [TcTyVar])
tcInstSkolTyKiVarsPushLevel skol_info_ki skol_info subst kvs tvs = do
  tc_lvl <- getTcLevel
  let !pushed_lvl = pushTcLevel tc_lvl
  tcInstSkolTyKiVarsAt skol_info_ki skol_info pushed_lvl subst kvs tvs

tcInstSkolTyKiVarsAt
  :: SkolemInfo
  -> SkolemInfo
  -> TcLevel
  -> Subst Tc Tc
  -> [KiVar Tc] -> [TyVar Tc]
  -> TcM (Subst Tc Tc, [TcKiVar], [TcTyVar])
tcInstSkolTyKiVarsAt skol_info_ki skol_info lvl subst kvs tvs
  = freshenTyKiVarsX new_skol_kv new_skol_tv subst kvs tvs
  where
    sk_details_ki = SkolemVar skol_info_ki lvl
    new_skol_kv name = mkTcKiVar name sk_details_ki
    sk_details = SkolemVar skol_info lvl
    new_skol_tv name kind = mkTcTyVar name kind sk_details

instantiateTyKiVarsX
  :: (Name -> TcM TcKiVar) -- TODO: TcKiVar instead
  -> (Name -> MonoKind Tc -> TcM TcTyVar)
  -> Subst Tc Tc -> [KiVar Tc] -> [TyVar Tc]
  -> TcM (Subst Tc Tc, [TcKiVar], [TcTyVar])
instantiateTyKiVarsX mk_kv mk_tv subst kvs tvs = do
  (subst', kvs') <- instantiateKiVarsX mk_kv subst kvs
  (subst'', tvs') <- instantiateTyVarsX mk_tv subst' tvs
  return (subst'', kvs', tvs')

instantiateTyVarsX
  :: (Name -> MonoKind Tc -> TcM TcTyVar)
  -> Subst Tc Tc -> [TyVar Tc]
  -> TcM (Subst Tc Tc, [TcTyVar])
instantiateTyVarsX mk_tv subst tvs
  = case tvs of
      [] -> return (subst, [])
      (tv:tvs) -> do let kind1 = substMonoKiUnchecked subst (varKind tv)
                     tv' <- mk_tv (varName tv) kind1
                     let subst1 = extendTvSubstWithClone subst tv (TcTyVar tv')
                     (subst', tvs') <- instantiateTyVarsX mk_tv subst1 tvs
                     return (subst', tv':tvs')

instantiateKiVarsX
  :: (Name -> TcM TcKiVar)
  -> Subst Tc Tc -> [KiVar Tc]
  -> TcM (Subst Tc Tc, [TcKiVar])
instantiateKiVarsX mk_kv kvsubst kvs
  = case kvs of
      [] -> return (kvsubst, [])
      (kv:kvs) -> do kv' <- mk_kv (varName kv)
                     let subst1 = extendKvSubstWithClone kvsubst kv (TcKiVar kv')
                     (kvsubst', kvs') <- instantiateKiVarsX mk_kv subst1 kvs
                     return (kvsubst', (kv':kvs'))  

freshenTyKiVarsX
  :: (Name -> TcKiVar)
  -> (Name -> MonoKind Tc -> TcTyVar)
  -> Subst Tc Tc -> [KiVar Tc] -> [TyVar Tc]
  -> TcM (Subst Tc Tc, [TcKiVar], [TcTyVar])
freshenTyKiVarsX mk_kv mk_tv = instantiateTyKiVarsX freshen_kv freshen_tv
  where
    freshen_kv :: Name -> TcM TcKiVar 
    freshen_kv name = do
      loc <- getSrcSpanM
      uniq <- newUnique
      let !occ_name = getOccName name
          new_name = mkInternalName uniq occ_name loc
      return (mk_kv new_name)

    freshen_tv :: Name -> MonoKind Tc -> TcM TcTyVar
    freshen_tv name kind = do
      loc <- getSrcSpanM
      uniq <- newUnique
      let !occ_name = getOccName name
          new_name = mkInternalName uniq occ_name loc
      return (mk_tv new_name kind)
