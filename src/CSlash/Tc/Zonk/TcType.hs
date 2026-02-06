{-# LANGUAGE FlexibleContexts #-}

module CSlash.Tc.Zonk.TcType
  ( module CSlash.Tc.Zonk.Monad
  ,  module CSlash.Tc.Zonk.TcType
  ) where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Types.Name
import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Unique.Set

import CSlash.Tc.Errors.Types
import CSlash.Tc.Errors.Ppr
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.TcRef
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Types.BasicTypes
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Zonk.Monad

-- import GHC.Core.InstEnv (ClsInst(is_tys))
import CSlash.Core.Type.Rep
import CSlash.Core.Type.Compare
import CSlash.Core.Type.Tidy
import CSlash.Core.TyCon
import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Core.Kind.FVs
import CSlash.Core.Kind.Compare
-- import GHC.Core.Coercion
import CSlash.Core.Predicate

import CSlash.Utils.Constants
import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Monad ( mapAccumLM )
import CSlash.Utils.Panic

import CSlash.Data.Bag
import CSlash.Data.Pair

{- *********************************************************************
*                                                                      *
                    Writing to metavariables
*                                                                      *
********************************************************************* -}

writeMetaTyVar :: HasDebugCallStack => TcTyVar -> Type Tc -> ZonkM ()
writeMetaTyVar tyvar ty
  | not debugIsOn
  = writeMetaTyVarRef tyvar (metaVarRef tyvar) ty
  | MetaVar { mv_ref = ref } <- tcVarDetails tyvar
  = writeMetaTyVarRef tyvar ref ty
  | otherwise
  = massertPpr False (text "Writing to non-meta tyvar" <+> ppr tyvar)
{-# INLINE writeMetaTyVar #-}

writeMetaTyVarRef
  :: HasDebugCallStack
  => TcTyVar 
  -> TcRef (MetaDetails (Type Tc))
  -> Type Tc
  -> ZonkM ()
writeMetaTyVarRef tyvar ref ty 
  | not debugIsOn
  = do traceZonk "writeMetaTyVar" (ppr tyvar <+> colon <+> ppr (varKind tyvar)
                                   <+> text ":=" <+> ppr ty)
       writeTcRef ref (Indirect ty)
  | otherwise
  = do meta_details <- readTcRef ref
       let tv_kind = varKind tyvar
           tv_lvl = varLevel tyvar
       zonked_tv_kind <- zonkTcMonoKind tv_kind
       zonked_ty <- zonkTcType ty
       let zonked_ty_kind = typeKind zonked_ty
           zonked_ty_lvl = tcTypeLevel zonked_ty
           level_check_ok = not (zonked_ty_lvl `strictlyDeeperThan` tv_lvl)
           level_check_msg = ppr zonked_ty_lvl $$ ppr tv_lvl
                             $$ ppr tyvar $$ ppr ty $$ ppr zonked_ty
           kind_check_ok = zonked_ty_kind `eqKind` Mono zonked_tv_kind
           kind_msg = hang (text "Ill-kinded update to meta tyvar")
                           2 (ppr tyvar <+> colon <+> (ppr tv_kind $$ ppr zonked_tv_kind)
                              <+> text ":="
                              <+> ppr ty <+> colon <+> (ppr zonked_ty_kind))
       traceZonk "writeMetaTyVar" (ppr tyvar <+> text ":=" <+> ppr ty)

       massertPpr (isFlexi meta_details) (double_upd_msg meta_details)

       massertPpr level_check_ok level_check_msg

       massertPpr kind_check_ok kind_msg

       writeTcRef ref (Indirect ty)
  where
    double_upd_msg details = hang (text "Double update of meta tyvar")
                                  2 (ppr tyvar $$ ppr details)
{-# INLINE writeMetaTyVarRef #-}

writeMetaKiVar :: HasDebugCallStack => TcKiVar -> MonoKind Tc -> ZonkM ()
writeMetaKiVar kivar ki
  | not debugIsOn
  = writeMetaKiVarRef kivar (metaVarRef kivar) ki
  | MetaVar { mv_ref = ref } <- tcVarDetails kivar
  = writeMetaKiVarRef kivar ref ki
  | otherwise
  = massertPpr False (text "Writing to non-meta kivar" <+> ppr kivar)
{-# INLINE writeMetaKiVar #-}

writeMetaKiVarRef
  :: HasDebugCallStack => TcKiVar -> TcRef (MetaDetails (MonoKind Tc)) -> MonoKind Tc -> ZonkM ()
writeMetaKiVarRef kivar ref ki
  | not debugIsOn
  = do traceZonk "writeMetaKiVar" (ppr kivar <+> text ":=" <+> ppr ki)
       writeTcRef ref (Indirect ki)
  | otherwise
  = do meta_details <- readTcRef ref
       zonked_ki <- zonkTcMonoKind ki
       let zonked_ki_lvl = tcMonoKindLevel zonked_ki
           kv_lvl = varLevel kivar
           level_check_ok = not (zonked_ki_lvl `strictlyDeeperThan` kv_lvl)
           level_check_msg = ppr zonked_ki_lvl $$ ppr kv_lvl
                             $$ ppr kivar $$ ppr ki $$ ppr zonked_ki

       traceZonk "writeMetaKiVar" (ppr kivar <+> text ":=" <+> ppr ki)

       massertPpr (isFlexi meta_details) (double_upd_msg meta_details)

       massertPpr level_check_ok level_check_msg

       writeTcRef ref (Indirect ki)
   where
     double_upd_msg details = hang (text "Double update of meta kivar")
                              2 (ppr kivar $$ ppr details)
{-# INLINE writeMetaKiVarRef #-}

{- *********************************************************************
*                                                                      *
              Zonking 
*                                                                      *
********************************************************************* -}

zonkTcType :: Type Tc -> ZonkM (Type Tc)
zonkTcTypes :: [Type Tc] -> ZonkM [Type Tc]
(zonkTcType, zonkTcTypes, _, _) = mapTyCo zonkTcTyCoMapper
  where
    zonkTcTyCoMapper
      :: TyCoMapper Tc Tc () ZonkM
    zonkTcTyCoMapper = TyCoMapper
      { tm_tyvar = const zonkTyVar
      , tm_covar = panic "tm_covar unused zonkTcType"
      , tm_hole = panic "tm_hole unused zonkTcType"
      , tm_tybinder = \_ tv _ k -> zonkVarKind tv >>= k ()
      , tm_kicobinder = \_ kcv k -> zonkVarKind kcv >>= k ()
      , tm_tylambinder = \_ tv k -> zonkVarKind tv >>= k ()
      , tm_tylamkibinder = \_ kv k -> k () kv
      , tm_tycon = zonkTcTyCon
      , tm_mkcm = zonkTcMonoKindMapper
      }

zonkTcTyCon :: TyCon Tc -> ZonkM (TyCon Tc)
zonkTcTyCon tc
  | Just ki <- monoTcTyConKind tc
  = do tck' <- zonkTcMonoKind ki
       return $ setTcTyConKind tc tck'
  | otherwise = return tc

zonkTyVar :: TyVar Tc -> ZonkM (Type Tc)
zonkTyVar (TcTyVar tctv) = zonkTcTyVar tctv
zonkTyVar tv = mkTyVarTy <$> zonkVarKind tv

zonkTcTyVar :: TcTyVar -> ZonkM (Type Tc)
zonkTcTyVar tv = case tcVarDetails tv of
  SkolemVar {} -> simple
  MetaVar { mv_ref = ref } -> do
    cts <- readTcRef ref
    case cts of
      Flexi -> simple
      Indirect ty -> do zty <- zonkTcType ty
                        writeTcRef ref (Indirect zty)
                        return zty
  where
    simple = do z_tv <- zonkVarKind tv
                return $ mkTyVarTy $ TcTyVar z_tv

zonkTcTyVarsToTcTyVars :: HasDebugCallStack => [TcTyVar] -> ZonkM [TcTyVar]
zonkTcTyVarsToTcTyVars = mapM zonkTcTyVarToTcTyVar

zonkTcTyVarToTcTyVar :: HasDebugCallStack => TcTyVar -> ZonkM TcTyVar
zonkTcTyVarToTcTyVar tv = do
  ty <- zonkTcTyVar tv
  let tv' = case getTyVar_maybe ty of
              Just tv'| Just tv'' <- toTcTyVar_maybe tv' -> tv''
              _ -> pprPanic "zonkTcTyVarToTcTyVar" (ppr tv $$ ppr ty)
  return tv'

{- *********************************************************************
*                                                                      *
              Zonking types
*                                                                      *
********************************************************************* -}

zonkVarKind :: VarHasKind tv Tc => tv -> ZonkM tv
zonkVarKind tv = do
  kind' <- zonkTcMonoKind $ varKind tv
  return $ setVarKind tv kind'

{- *********************************************************************
*                                                                      *
              Zonking kinds
*                                                                      *
********************************************************************* -}

zonkTcMonoKind :: (MonoKind Tc) -> ZonkM (MonoKind Tc)
zonkTcMonoKinds :: [MonoKind Tc] -> ZonkM [MonoKind Tc]
zonkKiCo :: KindCoercion Tc -> ZonkM (KindCoercion Tc)
(zonkTcMonoKind, zonkTcMonoKinds, zonkKiCo, _) = mapMKiCo zonkTcMonoKindMapper

zonkTcKind :: Kind Tc -> ZonkM (Kind Tc)
zonkTcKinds :: [Kind Tc] -> ZonkM [Kind Tc]
(zonkTcKind, zonkTcKinds) = mapKind zonkTcKindMapper

zonkTcKindMapper
  :: KiCoMapper Tc Tc () ZonkM
zonkTcKindMapper = KiCoMapper
  { kcm_kibinder = \_ kv k -> k () kv
  , kcm_mkcm = zonkTcMonoKindMapper
  }

zonkTcMonoKindMapper
  :: MKiCoMapper Tc Tc () ZonkM
zonkTcMonoKindMapper = MKiCoMapper
  { mkcm_kivar = const zonkKiVar
  , mkcm_covar = const (\cv -> mkKiCoVarCo <$> zonkVarKind cv)
  , mkcm_hole = hole }
  where
    hole :: () -> KindCoercionHole -> ZonkM (KindCoercion Tc)
    hole _ hole@(KindCoercionHole { kch_ref = ref, kch_co_var = cv }) = do
      contents <- readTcRef ref
      case contents of
        Just co -> do co' <- zonkKiCo co
                      checkKiCoercionHole cv co'
        Nothing -> do cv' <- zonkVarKind cv
                      return $ HoleCo $ hole { kch_co_var = cv' }

zonkKiVarsAndFV :: KiVarSet Tc -> ZonkM (KiVarSet Tc)
zonkKiVarsAndFV kivars = varsOfMonoKinds <$> mapM zonkKiVar (nonDetEltsUniqSet kivars)

zonkKiVar :: KiVar Tc -> ZonkM (MonoKind Tc)
zonkKiVar (TcKiVar tckv) = zonkTcKiVar tckv
zonkKiVar kv = return $ mkKiVarKi kv

zonkTcKiVar :: TcKiVar -> ZonkM (MonoKind Tc)
zonkTcKiVar kv 
  = case tcVarDetails kv of
      SkolemVar {} -> simple
      MetaVar { mv_ref = ref } -> do
        cts <- readTcRef ref
        case cts of
          Flexi -> simple
          Indirect ki -> do
            zki <- zonkTcMonoKind ki
            writeTcRef ref (Indirect zki)
            return zki
  where
    simple = return $ mkKiVarKi $ TcKiVar kv

zonkTcKiVarsToTcKiVars :: HasDebugCallStack => [TcKiVar] -> ZonkM [TcKiVar]
zonkTcKiVarsToTcKiVars = mapM zonkTcKiVarToTcKiVar

zonkTcKiVarToTcKiVar :: HasDebugCallStack => TcKiVar -> ZonkM TcKiVar
zonkTcKiVarToTcKiVar kv = do 
  ki <- zonkTcKiVar kv
  let kv' = case getKiVar_maybe ki of
              Just kv' | Just kv'' <- toTcKiVar_maybe kv' -> kv''
              _ -> pprPanic "zonkTcKiVarToTcKiVar" (panic "ppr kv $$ ppr ki")
  return kv'

{- *********************************************************************
*                                                                      *
              Coercion Holes
*                                                                      *
********************************************************************* -}

checkTyCoercionHole
  :: TyCoVar Tc
  -> TypeCoercion Tc
  -> ZonkM (TypeCoercion Tc)
checkTyCoercionHole cv co
  | debugIsOn
  = do cv_ty <- zonkTcType (varType cv)
       return
         $ assertPpr (ok cv_ty)
         (text "Bag type coercion hole" <+>
          ppr cv <> colon <+> vcat [ panic "ppr t1, ppr t2", ppr cv_ty ])
         co
  | otherwise
  = return co
  where
    (Pair t1 t2) = panic "tyCoercionParts co"
    ok cv_ty | TyEqPred cv_t1 cv_t2 <- classifyPredType cv_ty
             = t1 `eqType` cv_t1
               && t2 `eqType` cv_t2
             | otherwise
             = False

checkKiCoercionHole :: TcKiCoVar -> KindCoercion Tc -> ZonkM (KindCoercion Tc)
checkKiCoercionHole kcv kco
  | debugIsOn
  = do kcv_ki <- zonkTcMonoKind (varKind kcv)
       return
         $ assertPpr (ok kcv_ki)
         (text "Bad kind coercion hole"
          <+> ppr kcv <> colon <+> vcat [ ppr k1, ppr kc, ppr k2, ppr kcv_ki ])
         kco
  | otherwise
  = return kco
  where
    (kc, Pair k1 k2) = kiCoercionParts kco
    ok kcv_ki | KiCoPred kcv_kc kcv_k1 kcv_k2 <- classifyPredKind kcv_ki
              = k1 `eqMonoKind` kcv_k1
                && k2 `eqMonoKind` kcv_k2
                && kcv_kc == kc
              | otherwise
              = False

{- *********************************************************************
*                                                                      *
              Zonking constraints
*                                                                      *
********************************************************************* -}

zonkTyImplication :: TyImplication -> ZonkM TyImplication
zonkTyImplication implic@(TyImplic { tic_skols = skols
                                   , tic_given = given
                                   , tic_wanted = wanted
                                   , tic_info = info })
  = do skols' <- mapM zonkVarKind skols
       given' <- mapM zonkTyCoVar given
       info' <- zonkSkolemInfoAnon info
       wanted' <- zonkWTCRec wanted
       return (implic { tic_skols = skols'
                      , tic_given = given'
                      , tic_wanted = wanted'
                      , tic_info = info' })

zonkTyCoVar :: TyCoVar Tc -> ZonkM (TyCoVar Tc)
zonkTyCoVar var = updateVarTypeM zonkTcType var

zonkImplication :: KiImplication -> ZonkM KiImplication
zonkImplication implic@(KiImplic { kic_skols = skols
                               , kic_given = given
                               , kic_wanted = wanted
                               , kic_info = info }) = do
  given' <- mapM zonkVarKind given
  info' <- zonkSkolemInfoAnon info
  wanted' <- zonkWKCRec wanted
  return $ implic { kic_skols = skols
                  , kic_given = given'
                  , kic_wanted = wanted'
                  , kic_info = info' }

zonkKiCoVar :: KiCoVar Tc -> ZonkM (KiCoVar Tc)
zonkKiCoVar var = updateVarKindM zonkTcMonoKind var

zonkWTC :: WantedTyConstraints -> ZonkM WantedTyConstraints
zonkWTC wc = zonkWTCRec wc

zonkWKC :: WantedKiConstraints -> ZonkM WantedKiConstraints
zonkWKC wc = zonkWKCRec wc

zonkWTCRec :: WantedTyConstraints -> ZonkM WantedTyConstraints
zonkWTCRec (WTC { wtc_simple = simple, wtc_impl = implic, wtc_wkc = wkc })
  = do simple' <- zonkTySimples simple
       implic' <- mapBagM zonkTyImplication implic
       wkc' <- zonkWKCRec wkc
       return (WTC { wtc_simple = simple', wtc_impl = implic, wtc_wkc = wkc' })

zonkWKCRec :: WantedKiConstraints -> ZonkM WantedKiConstraints
zonkWKCRec (WKC { wkc_simple = simple, wkc_impl = implic }) = do
  simple' <- zonkKiSimples simple
  implic' <- mapBagM zonkImplication implic
  return $ WKC { wkc_simple = simple', wkc_impl = implic' }

zonkTySimples :: TyCts -> ZonkM TyCts
zonkTySimples cts = do
  cts' <- mapBagM zonkTyCt cts
  traceZonk "zonkSimples done:" (ppr cts')
  return cts'

zonkKiSimples :: KiCts -> ZonkM KiCts
zonkKiSimples cts = do
  cts' <- mapBagM zonkKiCt cts
  traceZonk "zonkSimples done:" (ppr cts')
  return cts'

zonkTyCt :: TyCt -> ZonkM TyCt
zonkTyCt (CTyEqCan (TyEqCt { teq_ev = ev })) = mkNonCanonicalTy <$> zonkCtTyEvidence ev
zonkTyCt (CIrredCanTy ir@(IrredTyCt { itr_ev = ev })) = do
  ev' <- zonkCtTyEvidence ev
  return $ CIrredCanTy $ ir { itr_ev = ev' }
zonkTyCt ct = do
  fl' <- zonkCtTyEvidence (ctTyEvidence ct)
  return $ mkNonCanonicalTy fl'

zonkKiCt :: KiCt -> ZonkM KiCt
zonkKiCt (CKiCoCan (KiCoCt { kc_ev = ev })) = mkNonCanonicalKi <$> zonkCtKiEvidence ev
zonkKiCt (CIrredCanKi ir@(IrredKiCt { ikr_ev = ev })) = do
  ev' <- zonkCtKiEvidence ev
  return $ CIrredCanKi $ ir { ikr_ev = ev' }
zonkKiCt ct = do
  fl' <- zonkCtKiEvidence (ctKiEvidence ct)
  return $ mkNonCanonicalKi fl'

zonkCtTyEvidence :: CtTyEvidence -> ZonkM CtTyEvidence
zonkCtTyEvidence ctev = do
  let pred = cttev_pred ctev
  pred' <- zonkTcType pred
  return $ setCtEvPredType ctev pred'

zonkCtKiEvidence :: CtKiEvidence -> ZonkM CtKiEvidence
zonkCtKiEvidence ctev = do
  let pred = ctkev_pred ctev
  pred' <- zonkTcMonoKind pred
  return $ setCtEvPredKind ctev pred'

zonkSkolemInfo :: SkolemInfo -> ZonkM SkolemInfo
zonkSkolemInfo (SkolemInfo u sk) = SkolemInfo u <$> zonkSkolemInfoAnon sk

zonkSkolemInfoAnon :: SkolemInfoAnon -> ZonkM SkolemInfoAnon
zonkSkolemInfoAnon (SigSkol cx ty kv_prs kcv_prs tv_prs) = do
  ty' <- zonkTcType ty
  return $ SigSkol cx ty' kv_prs kcv_prs tv_prs
zonkSkolemInfoAnon (InferSkol ntys) = do
  ntys' <- panic "mapM do_one ntys"
  return $ InferSkol ntys'
  where
    do_one (n, ty) = do
      ty' <- zonkTcType ty
      return (n, ty')
zonkSkolemInfoAnon skol_info = return skol_info

{- *********************************************************************
*                                                                      *
                 Tidying
*                                                                      *
********************************************************************** -}

tcInitTidyEnv :: ZonkM (TidyEnv Tc)
tcInitTidyEnv = do
  ZonkGblEnv { zge_binder_stack = bndrs } <- getZonkGblEnv
  go emptyTidyEnv bndrs
  where
    go :: TidyEnv Tc -> TcBinderStack -> ZonkM (TidyEnv Tc)
    go (env, tsubst, kcsubst, ksubst) [] = return (env, tsubst, kcsubst, ksubst)
    go (env, tsubst, kcsubst, ksubst) (b : bs)
      | TcTvBndr name tyvar <- b
      = do let (env', occ') = tidyOccName env (nameOccName name)
               name' = tidyNameOcc name occ'
               tyvar1 = setVarName tyvar name'
           tyvar2 <- zonkTcTyVarToTcTyVar tyvar1
           go (env', extendVarEnv tsubst (TcTyVar tyvar) (TcTyVar tyvar2), kcsubst, ksubst) bs
      | TcKvBndr name kivar <- b
      = do let (env', occ') = tidyOccName env (nameOccName name)
               name' = tidyNameOcc name occ'
               kivar1 = setVarName kivar name'
           kivar2 <- zonkTcKiVarToTcKiVar kivar1
           go (env', tsubst, kcsubst, extendVarEnv ksubst (TcKiVar kivar) (TcKiVar kivar2)) bs
      | otherwise
      = go (env, tsubst, kcsubst, ksubst) bs

tcInitOpenTidyEnv :: ([TyVar Tc], [KiCoVar Tc], [KiVar Tc]) -> ZonkM (TidyEnv Tc)
tcInitOpenTidyEnv vs = do
  env1 <- tcInitTidyEnv
  let env2 = tidyFreeVars env1 vs
  return env2

zonkTidyTcType :: TidyEnv Tc -> Type Tc -> ZonkM (TidyEnv Tc, Type Tc)
zonkTidyTcType env ty = do
  ty' <- zonkTcType ty
  return (tidyOpenTypeX env ty')

zonkTidyTcMonoKind :: TidyEnv Tc -> MonoKind Tc -> ZonkM (TidyEnv Tc, MonoKind Tc)
zonkTidyTcMonoKind env ki = do
  ki' <- zonkTcMonoKind ki
  return $ tidyOpenMonoKind env ki'

zonkTidyOrigin :: TidyEnv Tc -> CtOrigin -> ZonkM (TidyEnv Tc, CtOrigin)

zonkTidyOrigin env (GivenOrigin skol_info) = do
  skol_info1 <- zonkSkolemInfoAnon skol_info
  let skol_info2 = tidySkolemInfoAnon env skol_info1
  return (env, GivenOrigin skol_info2)

zonkTidyOrigin env orig@(TypeEqOrigin { uo_actual = act, uo_expected = exp }) = do
  (env1, act') <- zonkTidyTcType env act
  (env2, exp') <- zonkTidyTcType env1 exp
  return (env2, orig { uo_actual = act', uo_expected = exp' })

zonkTidyOrigin env (KindEqOrigin t1 t2 orig) = do
  (env1, t1') <- zonkTidyTcType env t1
  (env2, t2') <- zonkTidyTcType env1 t2
  (env3, orig') <- zonkTidyOrigin env2 orig
  return (env2, KindEqOrigin t1' t2' orig')

zonkTidyOrigin env orig@(KindCoOrigin { kco_actual = act, kco_expected = exp }) = do
  (env1, act') <- zonkTidyTcMonoKind env act
  (env2, exp') <- zonkTidyTcMonoKind env1 exp
  return (env2, orig { kco_actual = act', kco_expected = exp' })

zonkTidyOrigin env orig = return (env, orig)

tidyTyCt :: TidyEnv Tc -> TyCt -> TyCt
tidyTyCt env = updTyCtEvidence (tidyTyCtEvidence env)

tidyTyCtEvidence :: TidyEnv Tc -> CtTyEvidence -> CtTyEvidence
tidyTyCtEvidence env ctev = ctev { cttev_pred = tidyType env ty }
  where
    ty = cttev_pred ctev

tidyKiCt :: TidyEnv Tc -> KiCt -> KiCt
tidyKiCt env = updKiCtEvidence (tidyKiCtEvidence env)

tidyKiCtEvidence :: TidyEnv Tc -> CtKiEvidence -> CtKiEvidence
tidyKiCtEvidence env ctev = ctev { ctkev_pred = tidyMonoKind env ki }
  where
    ki = ctkev_pred ctev

-- GHC's 'tidyEvVar'
tidyTyCoVar
  :: TidyEnv Tc
  -> TyCoVar Tc
  -> TyCoVar Tc
tidyTyCoVar env var = updateVarType (tidyType env) var

tidyKiCoVar :: TidyEnv Tc -> KiCoVar Tc -> KiCoVar Tc
tidyKiCoVar env var = updateVarKind (tidyMonoKind env) var
