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
  -> SigmaType Tc
  -> TcM (CsWrapper Tc, [(Name, TcKiVar)], [(Name, TcKiCoVar)], [(Name, TcTyVar)], RhoType Tc)
topSkolemize skol_info ty = go init_subst idCsWrapper [] [] [] ty
  where
    init_subst = mkEmptySubst (varsOfType ty) (emptyVarSet, emptyVarSet, emptyVarSet)

    go subst wrap kv_prs kcv_prs tv_prs ty
      | (kvs, kcvs, tvs, inner_ty) <- tcSplitSigma ty
      , not (null kvs && null kcvs && null tvs)
      = do (subst', tckvs1, tckcvs1, tctvs1)
             <- tcInstSkolVarsX skol_info subst kvs kcvs tvs
           let kvs1 = TcKiVar <$> tckvs1
               kcvs1 = TcCoVar <$> tckcvs1
               tvs1 = TcTyVar <$> tctvs1
           traceTc "topSkol"
             $ vcat [ ppr kvs <+> vcat (map (ppr . getSrcSpan) kvs)
                    , ppr kvs1 <+> vcat (map (ppr . getSrcSpan) kvs1)
                    , ppr kcvs <+> vcat (map (ppr . getSrcSpan) kcvs)
                    , ppr kcvs1 <+> vcat (map (ppr . getSrcSpan) kcvs1)
                    , ppr tvs <+> vcat (map (ppr . getSrcSpan) tvs)
                    , ppr tvs1 <+> vcat (map (ppr . getSrcSpan) tvs1) ]
           go subst' (wrap <.> mkWpKiLams kvs1 <.> mkWpKiCoLams kcvs1 <.> mkWpTyLams tvs1)
                     (kv_prs ++ (map varName kvs `zip` tckvs1))
                     (kcv_prs ++ (map varName kcvs `zip` tckcvs1))
                     (tv_prs ++ (map varName tvs `zip` tctvs1))
                     inner_ty
      | otherwise
      = do traceTc "topSkol done" empty
           return (wrap, kv_prs, kcv_prs, tv_prs, substTy subst ty)

skolemizeRequired
  :: SkolemInfo
  -> VisArity
  -> SigmaType Tc
  -> TcM ( VisArity
         , CsWrapper Tc
         , [Name], [TcKiVar]
         , [Name], [TcKiCoVar]
         , [Name], [ForAllBinder TcTyVar]
         , RhoType Tc)
skolemizeRequired skol_info n_req sigma
  = go n_req init_subst idCsWrapper [] [] [] [] [] [] sigma
  where
    init_subst = mkEmptySubst (varsOfType sigma) (emptyVarSet, emptyVarSet, emptyVarSet)

    go n_req subst wrap kv_nms kv_acc kcv_nms kcv_acc tv_nms tv_acc ty
      | (n_req', kv_bndrs, kcv_bndrs, tv_bndrs, inner_ty)
          <- tcSplitForAllTyVarsReqTVBindersN n_req ty
      , not (null kv_bndrs && null kcv_bndrs && null tv_bndrs)
      = do (subst', kvs1, kcvs1, tv_bndrs1)
             <- tcInstSkolVarBndrsX skol_info subst kv_bndrs kcv_bndrs tv_bndrs
           let tvs1 = TcTyVar <$> binderVars tv_bndrs1
           traceTc "TODO skolemizeRequired, not fixing tv vis in wrapper" empty
           go n_req' subst'
             (wrap <.> mkWpKiLams (TcKiVar <$> kvs1)
                   <.> mkWpKiCoLams (TcCoVar <$> kcvs1)
                   <.> mkWpTyLams tvs1)
             (kv_nms ++ map varName kv_bndrs)
             (kv_acc ++ kvs1)
             (kcv_nms ++ map varName kcv_bndrs)
             (kcv_acc ++ kcvs1)
             (tv_nms ++ map (varName . binderVar) tv_bndrs)
             (tv_acc ++ tv_bndrs1)
             inner_ty
      | otherwise
      = return (n_req, wrap, kv_nms, kv_acc, kcv_nms, kcv_acc, tv_nms, tv_acc, substTy subst ty)

topInstantiate :: CtOrigin -> SigmaType Tc -> TcM (CsWrapper Tc, RhoType Tc)
topInstantiate orig sigma
  | (kvs, body1) <- tcSplitBigLamKiVars sigma
  , (kcvs, body2) <- tcSplitForAllKiCoVars body1
  , (tvs, body3) <- tcSplitForAllInvisTyVars body2
  , not (null kvs && null kcvs && null tvs)
  = do (_, _, _, wrap1, body4) <- instantiateSigma orig kvs kcvs tvs body3 sigma
       (wrap2, body5) <- topInstantiate orig body4
       return (wrap2 <.> wrap1, body5)
  | otherwise
  = return (idCsWrapper, sigma)

-- TODO: Some of the 'tvs' are actually kicovars!
-- For now we deal with that here.
-- In the future (when tyvars and kicovars are distinct types),
-- this must accept a 'tvs' arg and a 'kcvs' arg.
instantiateSigma
  :: CtOrigin
  -> [KiVar Tc]
  -> [KiCoVar Tc]
  -> [TyVar Tc]
  -> SigmaType Tc
  -> SigmaType Tc-- the type before splitting of kvs, kcvs and tvs (for finding in_scope)
  -> TcM ([TcKiVar], [TcKiCoVar], [TcTyVar], CsWrapper Tc, SigmaType Tc)
instantiateSigma orig kvs kcvs tvs body_ty orig_type = do
  (subst1, inst_kvs) <- mapAccumLM newMetaKiVarX empty_subst kvs
  (subst2, inst_kcvs) <- mapAccumLM newMetaKiCoVarX subst1 kcvs
  (subst, inst_tvs) <- mapAccumLM newMetaTyVarX subst2 tvs
  traceTc "instantiateSigma" (ppr subst)
  let inst_body = substTy subst body_ty
      inst_kv_kis = mkKiVarKis $ TcKiVar <$> inst_kvs
      inst_kcv_kis = varKind <$> inst_kcvs
      inst_tv_tys = mkTyVarTys $ TcTyVar <$> inst_tvs
  wrap <- instCall orig inst_kv_kis inst_kcv_kis inst_tv_tys
  traceTc "Instantiating"
    $ vcat [ text "origin" <+> pprCtOrigin orig
           , text "kvs" <+> ppr kvs
           , text "kcvs" <+> ppr kcvs
           , text "tvs" <+> ppr tvs
           , text "type" <+> debugPprType body_ty
           , text "orig_type" <+> debugPprType orig_type
           , text "with" <+> vcat (map debugPprMonoKind inst_kv_kis
                                   ++ map ppr inst_kcvs
                                   ++ map debugPprType inst_tv_tys) ]
  return (inst_kvs, inst_kcvs, inst_tvs, wrap, inst_body)
  where
    empty_subst = mkEmptySubst (varsOfType orig_type) (emptyVarSet, emptyVarSet, emptyVarSet)

{- *********************************************************************
*                                                                      *
            Instantiating a call
*                                                                      *
********************************************************************* -}

instCall :: CtOrigin -> [MonoKind Tc] -> [PredKind Tc] -> [Type Tc] -> TcM (CsWrapper Tc)
instCall orig kis preds tys = do
  kco_app <- instCallConstraints orig preds
  return (mkWpTyApps tys <.> kco_app <.> mkWpKiApps kis)

instCallConstraints :: CtOrigin -> [PredKind Tc] -> TcM (CsWrapper Tc)
instCallConstraints orig preds
  | null preds
  = return idCsWrapper
  | otherwise
  = do kcos <- mapM (emitWantedKiEq orig) preds
       traceTc "instCallConstraints" (ppr kcos)
       return $ mkWpKiCoApps kcos

-- Used for *kind checking types*, NOT when type checking terms.
-- That is why this returns koercions not CsWrapper.
-- It is also ok to unify early here, rather than defer entirely to the solver.
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

tcInstSkolVarsX
  :: SkolemInfo
  -> Subst Tc Tc
  -> [KiVar Tc] -> [KiCoVar Tc] -> [TyVar Tc]
  -> TcM (Subst Tc Tc, [TcKiVar], [TcKiCoVar], [TcTyVar])
tcInstSkolVarsX = tcInstSkolVarsPushLevel

tcInstSkolTyVarsX
  :: SkolemInfo -> Subst Tc Tc -> [TyVar Tc] -> TcM (Subst Tc Tc, [TcTyVar])
tcInstSkolTyVarsX skol_info subs vars = do
  (subst', kivars, kicovars, tyvars)
    <- tcInstSkolVarsX skol_info subs [] [] vars
  massert (null kivars)
  massert (null kicovars)
  pure (subst', tyvars)

tcInstSkolVarBndrsX
  :: SkolemInfo
  -> Subst Tc Tc
  -> [KiVar Tc]
  -> [KiCoVar Tc]
  -> [ForAllBinder (TyVar Tc)]
  -> TcM (Subst Tc Tc, [TcKiVar], [TcKiCoVar], [ForAllBinder TcTyVar])
tcInstSkolVarBndrsX skol_info subst kvs kcvs tvbs = do
  (subst', kvs', kcvs', tvbs')
    <- tcInstSkolVarsX skol_info subst kvs kcvs (binderVars tvbs)
  pure (subst', kvs', kcvs', zipWith Bndr tvbs' flags)
  where
    flags = binderFlags tvbs
  
tcInstSkolVarsPushLevel
  :: SkolemInfo
  -> Subst Tc Tc
  -> [KiVar Tc] -> [KiCoVar Tc] -> [TyVar Tc]
  -> TcM (Subst Tc Tc, [TcKiVar], [TcKiCoVar], [TcTyVar])
tcInstSkolVarsPushLevel skol_info subst kvs kcvs tvs = do
  tc_lvl <- getTcLevel
  let !pushed_lvl = pushTcLevel tc_lvl
  tcInstSkolVarsAt skol_info pushed_lvl subst kvs kcvs tvs

tcInstSkolVarsAt
  :: SkolemInfo
  -> TcLevel
  -> Subst Tc Tc
  -> [KiVar Tc] -> [KiCoVar Tc] -> [TyVar Tc]
  -> TcM (Subst Tc Tc, [TcKiVar], [TcKiCoVar], [TcTyVar])
tcInstSkolVarsAt skol_info lvl subst kvs kcvs tvs
  = freshenVarsX new_skol_kv new_skol_kcv new_skol_tv subst kvs kcvs tvs
  where
    sk_details_kv = SkolemVar skol_info lvl
    new_skol_kv name = mkTcKiVar name sk_details_kv
    sk_details_kcv = SkolemVar skol_info lvl
    new_skol_kcv name kind = mkTcKiCoVar name kind sk_details_kcv
    sk_details_tv = SkolemVar skol_info lvl
    new_skol_tv name kind = mkTcTyVar name kind sk_details_tv

instantiateVarsX
  :: (Name -> TcM TcKiVar)
  -> (Name -> MonoKind Tc -> TcM TcKiCoVar)
  -> (Name -> MonoKind Tc -> TcM TcTyVar)
  -> Subst Tc Tc -> [KiVar Tc] -> [KiCoVar Tc] -> [TyVar Tc]
  -> TcM (Subst Tc Tc, [TcKiVar], [TcKiCoVar], [TcTyVar])
instantiateVarsX mk_kv mk_kcv mk_tv subst0 kvs kcvs tvs = do
  (subst1, kvs') <- instantiateKiVarsX mk_kv subst0 kvs
  (subst2, kcvs') <- instantiateKiCoVarsX mk_kcv subst1 kcvs
  (subst3, tvs') <- instantiateTyVarsX mk_tv subst2 tvs
  return (subst3, kvs', kcvs', tvs')

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

instantiateKiCoVarsX
  :: (Name -> MonoKind Tc -> TcM TcKiCoVar)
  -> Subst Tc Tc -> [KiCoVar Tc]
  -> TcM (Subst Tc Tc, [TcKiCoVar])
instantiateKiCoVarsX mk_kcv subst kcvs
  = case kcvs of
      [] -> return (subst, [])
      (kcv:kcvs) -> do let kind1 = substMonoKiUnchecked subst (varKind kcv)
                       kcv' <- mk_kcv (varName kcv) kind1
                       let subst1 = extendKCvSubstWithClone subst kcv (TcCoVar kcv')
                       (subst', kcvs') <- instantiateKiCoVarsX mk_kcv subst1 kcvs
                       return (subst', kcv':kcvs')

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

freshenVarsX
  :: (Name -> TcKiVar)
  -> (Name -> MonoKind Tc -> TcKiCoVar)
  -> (Name -> MonoKind Tc -> TcTyVar)
  -> Subst Tc Tc -> [KiVar Tc] -> [KiCoVar Tc] -> [TyVar Tc]
  -> TcM (Subst Tc Tc, [TcKiVar], [TcKiCoVar], [TcTyVar])
freshenVarsX mk_kv mk_kcv mk_tv = instantiateVarsX freshen_kv freshen_kcv freshen_tv
  where
    freshen_kv :: Name -> TcM TcKiVar 
    freshen_kv name = do
      loc <- getSrcSpanM
      uniq <- newUnique
      let !occ_name = getOccName name
          new_name = mkInternalName uniq occ_name loc
      return (mk_kv new_name)

    freshen_kcv :: Name -> MonoKind Tc -> TcM TcKiCoVar
    freshen_kcv name kind = do
      loc <- getSrcSpanM
      uniq <- newUnique
      let !occ_name = getOccName name
          new_name = mkInternalName uniq occ_name loc
      return (mk_kcv new_name kind) 

    freshen_tv :: Name -> MonoKind Tc -> TcM TcTyVar
    freshen_tv name kind = do
      loc <- getSrcSpanM
      uniq <- newUnique
      let !occ_name = getOccName name
          new_name = mkInternalName uniq occ_name loc
      return (mk_tv new_name kind)
