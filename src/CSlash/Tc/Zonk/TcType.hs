{-# LANGUAGE FlexibleContexts #-}

module CSlash.Tc.Zonk.TcType
  ( module CSlash.Tc.Zonk.Monad
  ,  module CSlash.Tc.Zonk.TcType
  ) where

import Prelude hiding ((<>))

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

writeMetaTyVar :: HasDebugCallStack => TcTyVar TcKiVar -> TcType -> ZonkM ()
writeMetaTyVar = undefined

writeMetaTyVarRef
  :: (HasDebugCallStack, IsTyVar tv kv)
  => TcTyVar AnyKiVar
  -> TcRef (MetaDetails (Type tv kv))
  -> Type tv kv
  -> ZonkM ()
writeMetaTyVarRef tyvar ref ty = panic "writeMetaTyVarRef"
  -- | not debugIsOn
  -- = do traceZonk "writeMetaTyVar" (ppr tyvar <+> colon <+> ppr (varKind tyvar)
  --                                  <+> text ":=" <+> ppr ty)
  --      writeTcRef ref (Indirect ty)
  -- | otherwise
  -- = do meta_details <- readTcRef ref
  --      let tv_kind = varKind tyvar
  --          tv_lvl = varLevel tyvar
  --      zonked_tv_kind <- zonkTcMonoKind tv_kind
  --      zonked_ty <- panic "zonkTcType ty"
  --      let zonked_ty_kind = panic "typeKind zonked_ty"
  --          zonked_ty_lvl = panic "tcTypeLevel zonked_ty"
  --          level_check_ok = not (zonked_ty_lvl `strictlyDeeperThan` tv_lvl)
  --          level_check_msg = ppr zonked_ty_lvl $$ ppr tv_lvl
  --                            $$ ppr tyvar $$ ppr ty $$ ppr zonked_ty
  --          kind_check_ok = zonked_ty_kind `eqKind` Mono zonked_tv_kind
  --          kind_msg = hang (text "Ill-kinded update to meta tyvar")
  --                          2 (ppr tyvar <+> colon <+> (ppr tv_kind $$ ppr zonked_tv_kind)
  --                             <+> text ":="
  --                             <+> ppr ty <+> colon <+> (ppr zonked_ty_kind))
  --      traceZonk "writeMetaTyVar" (ppr tyvar <+> text ":=" <+> ppr ty)

  --      massertPpr (isFlexi meta_details) (double_upd_msg meta_details)

  --      massertPpr level_check_ok level_check_msg

  --      massertPpr kind_check_ok kind_msg

  --      writeTcRef ref (Indirect ty)
  -- where
  --   double_upd_msg details = hang (text "Double update of meta tyvar")
  --                                 2 (ppr tyvar $$ ppr details)
{-# INLINE writeMetaTyVarRef #-}

writeMetaKiVar :: HasDebugCallStack => TcKiVar -> AnyMonoKind -> ZonkM ()
writeMetaKiVar kivar ki
  | not debugIsOn
  = writeMetaKiVarRef kivar (metaVarRef kivar) ki
  | MetaVar { mv_ref = ref } <- tcVarDetails kivar
  = writeMetaKiVarRef kivar ref ki
  | otherwise
  = massertPpr False (text "Writing to non-meta kivar" <+> ppr kivar)
{-# INLINE writeMetaKiVar #-}

writeMetaKiVarRef
  :: HasDebugCallStack => TcKiVar -> TcRef (MetaDetails AnyMonoKind) -> AnyMonoKind -> ZonkM ()
writeMetaKiVarRef kivar ref ki
  | not debugIsOn
  = do traceZonk "writeMetaKiVar" (ppr kivar <+> text ":=" <+> ppr ki)
       writeTcRef ref (Indirect ki)
  | otherwise
  = do meta_details <- readTcRef ref
       zonked_ki <- zonkTcMonoKind ki
       let zonked_ki_lvl = anyMonoKindLevel zonked_ki
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

zonkTcType :: AnyType -> ZonkM AnyType
zonkTcTypes :: [AnyType] -> ZonkM [AnyType]
(zonkTcType, zonkTcTypes) = mapType zonkTcTypeMapper
  where
    zonkTcTypeMapper
      :: TypeMapper
         (AnyTyVar AnyKiVar) AnyKiVar
         (AnyTyVar AnyKiVar) AnyKiVar
         () ZonkM
    zonkTcTypeMapper = TypeMapper
      { tm_tyvar = const zonkAnyTyVar
      , tm_tybinder = \_ tv _ k -> zonkTyVarKind tv >>= k ()
      , tm_tylambinder = \_ tv k -> zonkTyVarKind tv >>= k ()
      , tm_tylamkibinder = \_ kv k -> k () kv
      , tm_tycon = zonkTcTyCon
      , tm_mkcm = zonkTcMonoKindMapper
      }

zonkTcTyCon :: AnyTyCon -> ZonkM AnyTyCon
zonkTcTyCon tc
  | isMonoTcTyCon tc = do tck' <- zonkTcKind (tyConKind tc)
                          return $ setTcTyConKind tc tck'
  | otherwise = return tc

zonkAnyTyVar :: AnyTyVar AnyKiVar -> ZonkM AnyType
zonkAnyTyVar tv = handleAnyTv (const simple)
  (\ tv -> case tcVarDetails tv of
             SkolemVar {} -> simple
             MetaVar { mv_ref = ref } -> do
               cts <- readTcRef ref
               case cts of
                 Flexi -> simple
                 Indirect ty -> do zty <- zonkTcType ty
                                   writeTcRef ref (Indirect zty)
                                   return zty
  ) tv
  where
    simple = return $ mkTyVarTy tv

zonkTcTyVar :: TcTyVar AnyKiVar -> ZonkM AnyType
zonkTcTyVar tv
  -- | isTcTyVar tv
  = case tcVarDetails tv of
      SkolemVar {} -> panic "zonk_kind_and_return"
      MetaVar { mv_ref = ref } -> do
        cts <- panic "readTcRef ref"
        case cts of
          Flexi -> panic "zonk_kind_and_return"
          Indirect ty -> do
            zty <- zonkTcType ty
            panic "writeTcRef ref (Indirect zty)"
            return zty
  -- | otherwise
  -- = zonk_kind_and_return
  -- where
  --   zonk_kind_and_return = do
  --     z_tv <- zonkTyVarKind tv
  --     return $ mkTyVarTy z_tv

zonkTcTyVarsToTcTyVars :: HasDebugCallStack => [TcTyVar AnyKiVar] -> ZonkM [TcTyVar AnyKiVar]
zonkTcTyVarsToTcTyVars = mapM zonkTcTyVarToTcTyVar

zonkTcTyVarToTcTyVar :: HasDebugCallStack => TcTyVar AnyKiVar -> ZonkM (TcTyVar AnyKiVar)
zonkTcTyVarToTcTyVar tv = do
  ty <- zonkTcTyVar tv
  let tv' = case panic "getTyVar_maybe ty" of
              Just tv' -> tv'
              Nothing -> pprPanic "zonkTcTyVarToTcTyVar" (panic "ppr tv $$ ppr ty")
  return tv'

{- *********************************************************************
*                                                                      *
              Zonking types
*                                                                      *
********************************************************************* -}

zonkTyVarKind :: VarHasKind tv AnyKiVar => tv -> ZonkM tv
zonkTyVarKind tv = do
  kind' <- zonkTcMonoKind $ varKind tv
  return $ setVarKind tv kind'

{- *********************************************************************
*                                                                      *
              Zonking kinds
*                                                                      *
********************************************************************* -}

zonkTcMonoKind :: AnyMonoKind -> ZonkM AnyMonoKind
zonkTcMonoKinds :: [AnyMonoKind] -> ZonkM [AnyMonoKind]
zonkKiCo :: AnyKindCoercion -> ZonkM AnyKindCoercion
(zonkTcMonoKind, zonkTcMonoKinds, zonkKiCo, _) = mapMKiCo zonkTcMonoKindMapper

zonkTcKind :: AnyKind -> ZonkM AnyKind
zonkTcKinds :: [AnyKind] -> ZonkM [AnyKind]
(zonkTcKind, zonkTcKinds) = mapKind zonkTcKindMapper

zonkTcKindMapper
  :: KiCoMapper AnyKiVar AnyKiVar () ZonkM
zonkTcKindMapper = KiCoMapper
  { kcm_kibinder = \_ kv k -> k () kv
  , kcm_mkcm = zonkTcMonoKindMapper
  }

zonkTcMonoKindMapper
  :: MKiCoMapper AnyKiVar AnyKiVar () ZonkM
zonkTcMonoKindMapper = MKiCoMapper
  { mkcm_kivar = const zonkAnyKiVar
  , mkcm_covar = const (\cv -> mkKiCoVarCo <$> zonkKiCoVarKind cv)
  , mkcm_hole = hole }
  where
    hole :: () -> AnyKindCoercionHole -> ZonkM AnyKindCoercion
    hole _ hole@(CoercionHole { ch_ref = ref, ch_co_var = cv }) = do
      contents <- readTcRef ref
      case contents of
        Just co -> do co' <- zonkKiCo co
                      checkKiCoercionHole cv co'
        Nothing -> do cv' <- zonkKiCoVarKind cv
                      return $ HoleCo $ hole { ch_co_var = cv' }

zonkAnyKiVar :: AnyKiVar -> ZonkM AnyMonoKind
zonkAnyKiVar kv = handleAnyKv (const simple)
  (\ kv -> case tcVarDetails kv of
             SkolemVar {} -> simple
             MetaVar { mv_ref = ref } -> do
               cts <- readTcRef ref
               case cts of
                 Flexi -> simple
                 Indirect ki -> do zki <- zonkTcMonoKind ki
                                   writeTcRef ref (Indirect zki)
                                   return zki
  ) kv
  where
    simple = return $ mkKiVarKi kv

zonkAnyKiVarsAndFV :: AnyKiVarSet -> ZonkM AnyKiVarSet
zonkAnyKiVarsAndFV kivars = varsOfMonoKinds <$> mapM zonkAnyKiVar (nonDetEltsUniqSet kivars)

zonkTcKiVar :: TcKiVar -> ZonkM AnyMonoKind
zonkTcKiVar kv 
  = case tcVarDetails kv of
      SkolemVar {} -> return $ mkKiVarKi (toAnyKiVar kv)
      MetaVar { mv_ref = ref } -> do
        cts <- readTcRef ref
        case cts of
          Flexi -> return $ mkKiVarKi (toAnyKiVar kv)
          Indirect ki -> do
            zki <- zonkTcMonoKind ki
            writeTcRef ref (Indirect zki)
            return zki

zonkTcKiVarsToTcKiVars :: HasDebugCallStack => [TcKiVar] -> ZonkM [TcKiVar]
zonkTcKiVarsToTcKiVars = mapM zonkTcKiVarToTcKiVar

zonkTcKiVarToTcKiVar :: HasDebugCallStack => TcKiVar -> ZonkM TcKiVar
zonkTcKiVarToTcKiVar kv = do 
  ki <- zonkTcKiVar kv
  let kv' = case getKiVar_maybe ki of
              Just kv' | Just kv'' <- toTcKiVar_maybe kv' -> kv
              _ -> pprPanic "zonkTcKiVarToTcKiVar" (panic "ppr kv $$ ppr ki")
  return kv'

zonkKiCoVarKind :: KiCoVar AnyKiVar -> ZonkM (KiCoVar AnyKiVar)
zonkKiCoVarKind kcv = do
  kind' <- zonkTcMonoKind (varKind kcv)
  return $ setVarKind kcv kind'

{- *********************************************************************
*                                                                      *
              Kind Coercion Holes
*                                                                      *
********************************************************************* -}

checkKiCoercionHole :: KiCoVar AnyKiVar -> AnyKindCoercion -> ZonkM AnyKindCoercion
checkKiCoercionHole kcv kco
  | debugIsOn
  = do kcv_ki <- zonkTcMonoKind (varKind kcv)
       return
         $ assertPpr (ok kcv_ki)
         (text "Bad kind coercion hole"
          <+> ppr kcv <> colon <+> vcat [ ppr k1, ppr k2, ppr kcv_ki ])
         kco
  | otherwise
  = return kco
  where
    (kc, Pair k1 k2) = kiCoercionKind kco
    ok kcv_ki | KiCoPred kcv_kc kcv_k1 kcv_k2 <- classifyPredKind kcv_ki
              = k1 `eqMonoKind` kcv_k1
                && k2 `eqMonoKind` kcv_k2
                && kc == kcv_kc
              | otherwise
              = False

{- *********************************************************************
*                                                                      *
              Zonking constraints
*                                                                      *
********************************************************************* -}

zonkImplication :: Implication -> ZonkM Implication
zonkImplication implic@(Implic { ic_skols = skols
                               , ic_given = given
                               , ic_wanted = wanted
                               , ic_info = info }) = do
  given' <- mapM zonkKiCoVar given
  info' <- zonkSkolemInfoAnon info
  wanted' <- zonkWCRec wanted
  return $ implic { ic_skols = skols
                  , ic_given = given'
                  , ic_wanted = wanted'
                  , ic_info = info' }

zonkKiCoVar :: KiCoVar AnyKiVar -> ZonkM (KiCoVar AnyKiVar)
zonkKiCoVar var = updateVarKindM zonkTcMonoKind var

zonkWC :: WantedConstraints -> ZonkM WantedConstraints
zonkWC wc = zonkWCRec wc

zonkWCRec :: WantedConstraints -> ZonkM WantedConstraints
zonkWCRec (WC { wc_simple = simple, wc_impl = implic }) = do
  simple' <- zonkSimples simple
  implic' <- mapBagM zonkImplication implic
  return $ WC { wc_simple = simple', wc_impl = implic' }

zonkSimples :: Cts -> ZonkM Cts
zonkSimples cts = do
  cts' <- mapBagM zonkCt cts
  traceZonk "zonkSimples done:" (ppr cts')
  return cts'

zonkCt :: Ct -> ZonkM Ct
zonkCt (CKiCoCan (KiCoCt { kc_ev = ev })) = mkNonCanonical <$> zonkCtEvidence ev
zonkCt (CIrredCan ir@(IrredCt { ir_ev = ev })) = do
  ev' <- zonkCtEvidence ev
  return $ CIrredCan $ ir { ir_ev = ev' }
zonkCt ct = do
  fl' <- zonkCtEvidence (ctEvidence ct)
  return $ mkNonCanonical fl'

zonkCtEvidence :: CtEvidence -> ZonkM CtEvidence
zonkCtEvidence ctev = do
  let pred = ctev_pred ctev
  pred' <- zonkTcMonoKind pred
  return $ setCtEvPredKind ctev pred'

zonkSkolemInfo :: SkolemInfo -> ZonkM SkolemInfo
zonkSkolemInfo (SkolemInfo u sk) = SkolemInfo u <$> zonkSkolemInfoAnon sk

zonkSkolemInfoAnon :: SkolemInfoAnon -> ZonkM SkolemInfoAnon
zonkSkolemInfoAnon (SigSkol cx ty tv_prs) = do
  ty' <- panic "zonkTcType ty"
  return $ SigSkol cx ty' tv_prs
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

tcInitTidyEnv :: ZonkM AnyTidyEnv
tcInitTidyEnv = do
  ZonkGblEnv { zge_binder_stack = bndrs } <- getZonkGblEnv
  go emptyTidyEnv bndrs
  where
    go :: AnyTidyEnv -> TcBinderStack -> ZonkM AnyTidyEnv
    go (env, tsubst, ksubst) [] = return (env, tsubst, ksubst)
    go (env, tsubst, ksubst) (b : bs)
      | TcTvBndr name tyvar <- b
      = do let (env', occ') = tidyOccName env (nameOccName name)
               name' = tidyNameOcc name occ'
               tyvar1 = setVarName tyvar name'
           tyvar2 <- zonkTcTyVarToTcTyVar tyvar1
           go (env', extendVarEnv tsubst (toAnyTyVar tyvar) (toAnyTyVar tyvar2), ksubst) bs
      | TcKvBndr name kivar <- b
      = do let (env', occ') = tidyOccName env (nameOccName name)
               name' = tidyNameOcc name occ'
               kivar1 = setVarName kivar name'
           kivar2 <- handleAnyKv (return . toAnyKiVar)
                                 (toAnyKiVar <.$> zonkTcKiVarToTcKiVar) kivar1
           go (env', tsubst, extendVarEnv ksubst kivar kivar2) bs
      | otherwise
      = go (env, tsubst, ksubst) bs

tcInitOpenTidyEnv :: ([AnyTyVar AnyKiVar], [AnyKiVar]) -> ZonkM AnyTidyEnv
tcInitOpenTidyEnv (tvs, kvs) = do
  env1 <- tcInitTidyEnv
  let env2 = tidyFreeKiVars env1 kvs
      env3 = tidyFreeTyVars env2 tvs
  return env3

zonkTidyTcMonoKind :: AnyTidyEnv -> AnyMonoKind -> ZonkM (AnyTidyEnv, AnyMonoKind)
zonkTidyTcMonoKind env ki = do
  ki' <- zonkTcMonoKind ki
  return $ tidyOpenMonoKind env ki'

zonkTidyOrigin :: AnyTidyEnv -> CtOrigin -> ZonkM (AnyTidyEnv, CtOrigin)

zonkTidyOrigin env (GivenOrigin skol_info) = do
  skol_info1 <- zonkSkolemInfoAnon skol_info
  let skol_info2 = tidySkolemInfoAnon env skol_info1
  return (env, GivenOrigin skol_info2)

zonkTidyOrigin env orig@(KindCoOrigin { kco_actual = act, kco_expected = exp }) = do
  (env1, act') <- zonkTidyTcMonoKind env act
  (env2, exp') <- zonkTidyTcMonoKind env1 exp
  return (env2, orig { kco_actual = act', kco_expected = exp' })

zonkTidyOrigin env orig = return (env, orig)

tidyCt :: AnyTidyEnv -> Ct -> Ct
tidyCt env = updCtEvidence (tidyCtEvidence env)

tidyCtEvidence :: AnyTidyEnv -> CtEvidence -> CtEvidence
tidyCtEvidence env ctev = ctev { ctev_pred = tidyMonoKind env ki }
  where
    ki = ctev_pred ctev

tidyKiCoVar :: AnyTidyEnv -> KiCoVar AnyKiVar -> KiCoVar AnyKiVar
tidyKiCoVar env var = updateVarKind (tidyMonoKind env) var
