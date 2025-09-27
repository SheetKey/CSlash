{-# LANGUAGE BangPatterns #-}

module CSlash.Tc.Utils.Instantiate where

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
import CSlash.Core.Type.Subst
import CSlash.Core.Kind
import CSlash.Core.Kind.Subst
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
import CSlash.Types.Id
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
  -> AnySigmaType
  -> TcM (AnyCsWrapper, [(Name, AnyKiVar)], [(Name, AnyTyVar AnyKiVar)], AnyRhoType)
topSkolemize skolem_info_ki skolem_info ty = go init_subst idCsWrapper [] [] ty
  where
    init_subst = let (tvs, kcvs, kvs) = varsOfType ty
                     tvs' = tvs `unionVarSet` mapVarSet toAnyTyVar kcvs
                 in mkEmptyTvSubst (mkInScopeSet tvs', mkInScopeSet kvs)

    go subst wrap kv_prs tv_prs ty
      | (kvs, tvs, inner_ty) <- tcSplitSigma ty
      , not (null kvs && null tvs)
      = do (subst', kvs1, tctvs1) <- tcInstSkolTyKiVarsX skolem_info_ki skolem_info subst kvs tvs
           let tvs1 = toAnyTyVar <$> tctvs1
           traceTc "topSkol"
             $ vcat [ ppr kvs <+> vcat (map (ppr . getSrcSpan) kvs)
                    , ppr kvs1 <+> vcat (map (ppr . getSrcSpan) kvs1)
                    , ppr tvs <+> vcat (map (ppr . getSrcSpan) tvs)
                    , ppr tvs1 <+> vcat (map (ppr . getSrcSpan) tvs1) ]
           go subst' (wrap <.> mkWpKiLams kvs1 <.> mkWpTyLams tvs1)
                     (kv_prs ++ (map varName kvs `zip` kvs1))
                     (tv_prs ++ (map varName tvs `zip` tvs1))
                     inner_ty
      | otherwise
      = do traceTc "topSkol done" empty
           return (wrap, kv_prs, tv_prs, substTy subst ty)

skolemizeRequired
  :: SkolemInfo
  -> VisArity
  -> AnySigmaType
  -> TcM (VisArity, AnyCsWrapper, [Name], [ForAllBinder (TcTyVar AnyKiVar)], AnyRhoType)
skolemizeRequired skolem_info n_req sigma
  = go n_req init_subst idCsWrapper [] [] sigma
  where
    (tvs, kcvs, kvs) = varsOfType sigma
    tvs' = tvs `unionVarSet` mapVarSet toAnyTyVar kcvs
    init_subst = mkEmptyTvSubst (mkInScopeSet tvs', mkInScopeSet kvs)

    go n_req subst wrap acc_nms acc_bndrs ty
      | (n_req', bndrs, inner_ty) <- tcSplitForAllTyVarsReqTVBindersN n_req ty
      , not (null bndrs)
      = do (subst', bndrs1) <- tcInstSkolTyVarBndrsX skolem_info subst bndrs
           let tvs1 = toAnyTyVar <$> binderVars bndrs1
           traceTc "skolemizeRequired, not fixing tv vis in wrapper" empty
           go n_req' subst'
             (wrap <.> mkWpTyLams tvs1)
             (acc_nms ++ map (varName . binderVar) bndrs)
             (acc_bndrs ++ bndrs1)
             inner_ty
      | otherwise
      = return (n_req, wrap, acc_nms, acc_bndrs, substTy subst ty)

topInstantiate :: CtOrigin -> AnySigmaType -> TcM (AnyCsWrapper, AnyRhoType)
topInstantiate orig sigma
  | (kvs, body1) <- tcSplitBigLamKiVars sigma
  , (tvs, body2) <- tcSplitForAllInvisTyVars body1
  , not (null kvs && null tvs)
  = do (_, _, wrap1, body3) <- instantiateSigma orig kvs tvs body1 sigma
       (wrap2, body4) <- topInstantiate orig body3
       return (wrap2 <.> wrap1, body4)
  | otherwise
  = return (idCsWrapper, sigma)

instantiateSigma
  :: CtOrigin
  -> [AnyKiVar]
  -> [AnyTyVar AnyKiVar]
  -> AnySigmaType
  -> AnySigmaType -- the type before splitting of kvs and tvs (for finding in_scope)
  -> TcM ([AnyKiVar], [AnyTyVar AnyKiVar], AnyCsWrapper, AnySigmaType)
instantiateSigma orig kvs tvs body_ty orig_type = do
  (kv_subst, inst_kvs) <- mapAccumLM newMetaKiVarX empty_kv_subst kvs
  (subst, inst_tvs) <- mapAccumLM newMetaTyVarX (mk_empty_tv_subst kv_subst) tvs
  let inst_body = substTy subst body_ty
      inst_kv_kis = mkKiVarKis inst_kvs
      inst_tv_tys = mkTyVarTys inst_tvs
      wrap = mkWpTyApps inst_tv_tys <.> mkWpKiApps inst_kv_kis
  traceTc "Instantiating"
    $ vcat [ text "origin" <+> pprCtOrigin orig
           , text "kvs" <+> ppr kvs
           , text "tvs" <+> ppr tvs
           , text "type" <+> debugPprType body_ty
           , text "orig_type" <+> debugPprType orig_type
           , text "with" <+> vcat (map debugPprMonoKind inst_kv_kis
                                   ++ map debugPprType inst_tv_tys) ]
  return (inst_kvs, inst_tvs, wrap, inst_body)
  where
    (empty_kv_subst, mk_empty_tv_subst)
      = let (tvs, kcvs, kvs) = varsOfType orig_type
            tvs' = tvs `unionVarSet` mapVarSet toAnyTyVar kcvs
        in ( mkEmptyKvSubst (mkInScopeSet kvs)
           , mkTvSubstFromKvs (mkInScopeSet tvs') )

{- *********************************************************************
*                                                                      *
            Instantiating a call
*                                                                      *
********************************************************************* -}

{- *********************************************************************
*                                                                      *
         Instantiating Kinds
*                                                                      *
********************************************************************* -}

tcInstInvisibleKiBinder :: AnyKvSubst -> AnyKiVar -> TcM (AnyKvSubst, AnyType)
tcInstInvisibleKiBinder subst kv = do
  (subst', kv') <- newMetaKiVarX subst kv
  return (subst', Embed $ mkKiVarKi kv')

{- *********************************************************************
*                                                                      *
        SkolemTvs/Kvs (immutable)
*                                                                      *
********************************************************************* -}

tcInstSkolTyKiVarsX
  :: SkolemInfo
  -> SkolemInfo
  -> AnyTvSubst
  -> [AnyKiVar] -> [AnyTyVar AnyKiVar]
  -> TcM (AnyTvSubst, [AnyKiVar], [TcTyVar AnyKiVar])
tcInstSkolTyKiVarsX = tcInstSkolTyKiVarsPushLevel

tcInstSkolTyVarBndrsX
  :: SkolemInfo
  -> AnyTvSubst
  -> [ForAllBinder (AnyTyVar AnyKiVar)]
  -> TcM (AnyTvSubst, [ForAllBinder (TcTyVar AnyKiVar)])
tcInstSkolTyVarBndrsX skol_info subs bndrs = do
  (subst', kibndrs, bndrs') <- tcInstSkolTyKiVarsX skol_info skol_info subs [] (binderVars bndrs)
  massert (null kibndrs)
  pure (subst', zipWith Bndr bndrs' flags)
  where
    flags = binderFlags bndrs
  
tcInstSkolTyKiVarsPushLevel
  :: SkolemInfo
  -> SkolemInfo
  -> AnyTvSubst
  -> [AnyKiVar] -> [AnyTyVar AnyKiVar]
  -> TcM (AnyTvSubst, [AnyKiVar], [TcTyVar AnyKiVar])
tcInstSkolTyKiVarsPushLevel skol_info_ki skol_info subst kvs tvs = do
  tc_lvl <- getTcLevel
  let !pushed_lvl = pushTcLevel tc_lvl
  tcInstSkolTyKiVarsAt skol_info_ki skol_info pushed_lvl subst kvs tvs

tcInstSkolTyKiVarsAt
  :: SkolemInfo
  -> SkolemInfo
  -> TcLevel
  -> AnyTvSubst
  -> [AnyKiVar] -> [AnyTyVar AnyKiVar]
  -> TcM (AnyTvSubst, [AnyKiVar], [TcTyVar AnyKiVar])
tcInstSkolTyKiVarsAt skol_info_ki skol_info lvl subst kvs tvs
  = freshenTyKiVarsX new_skol_kv new_skol_tv subst kvs tvs
  where
    sk_details_ki = SkolemVar skol_info_ki lvl
    new_skol_kv name = toAnyKiVar $ mkTcKiVar name sk_details_ki
    sk_details = SkolemVar skol_info lvl
    new_skol_tv name kind = mkTcTyVar name kind sk_details

instantiateTyKiVarsX
  :: (Name -> TcM AnyKiVar)
  -> (Name -> AnyMonoKind -> TcM (TcTyVar AnyKiVar))
  -> AnyTvSubst -> [AnyKiVar] -> [AnyTyVar AnyKiVar]
  -> TcM (AnyTvSubst, [AnyKiVar], [TcTyVar AnyKiVar])
instantiateTyKiVarsX mk_kv mk_tv (TvSubst tis tenv kvsubst) kvs tvs = do
  (kvsubst', kvs') <- instantiateKiVarsX mk_kv kvsubst kvs
  (tvsubst', tvs') <- instantiateTyVarsX mk_tv (TvSubst tis tenv kvsubst') tvs
  return (tvsubst', kvs', tvs')

instantiateTyVarsX
  :: (Name -> AnyMonoKind -> TcM (TcTyVar AnyKiVar))
  -> AnyTvSubst -> [AnyTyVar AnyKiVar]
  -> TcM (AnyTvSubst, [TcTyVar AnyKiVar])
instantiateTyVarsX mk_tv subst@(TvSubst _ _ kvsubst) tvs
  = case tvs of
      [] -> return (subst, [])
      (tv:tvs) -> do let kind1 = substMonoKiUnchecked kvsubst (varKind tv)
                     tv' <- mk_tv (varName tv) kind1
                     let subst1 = extendTvSubstWithClone subst (toAnyTyVar tv) (toAnyTyVar tv')
                     (subst', tvs') <- instantiateTyVarsX mk_tv subst1 tvs
                     return (subst', tv':tvs')

instantiateKiVarsX
  :: (Name -> TcM AnyKiVar)
  -> AnyKvSubst -> [AnyKiVar]
  -> TcM (AnyKvSubst, [AnyKiVar])
instantiateKiVarsX mk_kv kvsubst kvs
  = case kvs of
      [] -> return (kvsubst, [])
      (kv:kvs) -> do kv' <- mk_kv (varName kv)
                     let subst1 = extendKvSubstWithClone kvsubst kv kv'
                     (kvsubst', kvs') <- instantiateKiVarsX mk_kv subst1 kvs
                     return (kvsubst', (kv':kvs'))  

freshenTyKiVarsX
  :: (Name -> AnyKiVar)
  -> (Name -> AnyMonoKind -> TcTyVar AnyKiVar)
  -> AnyTvSubst -> [AnyKiVar] -> [AnyTyVar AnyKiVar]
  -> TcM (AnyTvSubst, [AnyKiVar], [TcTyVar AnyKiVar])
freshenTyKiVarsX mk_kv mk_tv = instantiateTyKiVarsX freshen_kv freshen_tv
  where
    freshen_kv :: Name -> TcM AnyKiVar
    freshen_kv name = do
      loc <- getSrcSpanM
      uniq <- newUnique
      let !occ_name = getOccName name
          new_name = mkInternalName uniq occ_name loc
      return (mk_kv new_name)

    freshen_tv :: Name -> AnyMonoKind -> TcM (TcTyVar AnyKiVar)
    freshen_tv name kind = do
      loc <- getSrcSpanM
      uniq <- newUnique
      let !occ_name = getOccName name
          new_name = mkInternalName uniq occ_name loc
      return (mk_tv new_name kind)
