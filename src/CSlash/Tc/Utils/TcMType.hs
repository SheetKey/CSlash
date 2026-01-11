{-# LANGUAGE TupleSections #-}

module CSlash.Tc.Utils.TcMType where

import CSlash.Cs
import CSlash.Platform

import CSlash.Driver.DynFlags

import {-# SOURCE #-} CSlash.Tc.Utils.Unify ( tcSubMult, unifyInvisibleType )
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Utils.Monad        -- TcType, amongst others
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Errors.Types
import CSlash.Tc.Zonk.Type
import CSlash.Tc.Zonk.TcType

import CSlash.Builtin.Names

import CSlash.Core.ConLike
import CSlash.Core.DataCon
import CSlash.Core.Type
import CSlash.Core.Type.Rep
import CSlash.Core.Type.Ppr
import CSlash.Core.Type.Ppr
import CSlash.Core.Type.Subst
import CSlash.Core.Kind
import CSlash.Core.Kind.FVs
import CSlash.Core.Kind.Subst
import CSlash.Core.TyCon
-- import GHC.Core.Coercion
-- import GHC.Core.Class
import CSlash.Core.Predicate
import CSlash.Core.UsageEnv

import CSlash.Types.Var
import CSlash.Types.Id as Id
import CSlash.Types.Name hiding (varName)
import CSlash.Types.SourceText
import CSlash.Types.Var.Set

import CSlash.Builtin.Types
import CSlash.Types.Var.Env
import CSlash.Types.Unique.Set
import CSlash.Types.Basic ( TypeOrKind(..)
                          , NonStandardDefaultingStrategy(..)
                          , DefaultingStrategy(..), defaultNonStandardTyVars )

import CSlash.Data.FastString
import CSlash.Data.Bag

import CSlash.Utils.Misc
import CSlash.Utils.Trace
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Constants (debugIsOn)

import Control.Monad
import Data.IORef
import CSlash.Data.Maybe
import qualified Data.Semigroup as Semi
import CSlash.Types.Name.Reader

{- *********************************************************************
*                                                                      *
        Kind variables
*                                                                      *
********************************************************************* -}

newMetaKindVar :: TcM TcMonoKind
newMetaKindVar = do
  details <- newMetaDetails TauVar
  name <- newMetaKiVarName (fsLit "k")
  let kv = mkTcKiVar name details
  traceTc "newMetaKindVar" (ppr kv)
  return (mkKiVarKi kv)

newMetaKindVars :: Int -> TcM [TcMonoKind]
newMetaKindVars n = replicateM n newMetaKindVar

{- **********************************************************************
*                                                                       *
            Evidence variables
*                                                                       *
********************************************************************** -}

predTypeOccName :: IsTyVar tv kv => PredType tv kv -> OccName
predTypeOccName ty = case classifyPredType ty of
  TyEqPred {} -> mkVarOccFS (fsLit "tco")
  TyIrredPred {} -> mkVarOccFS (fsLit "tirred")
  ForAllPred {} -> mkVarOccFS (fsLit "df")

predKindOccName :: PredKind kv -> OccName
predKindOccName ki = case classifyPredKind ki of
  KiCoPred {} -> mkVarOccFS (fsLit "kco")
  IrredPred {} -> mkVarOccFS (fsLit "kirred")

newWantedWithLoc :: CtLoc -> AnyPredKind -> TcM CtKiEvidence
newWantedWithLoc loc predki = do
  dst <- case classifyPredKind predki of
           KiCoPred {} -> newKiCoercionHole predki
           _ -> pprPanic "newWantedWithLoc" $ vcat [ ppr predki ]
  return $ CtKiWanted { ctkev_dest = dst
                    , ctkev_pred = predki
                    , ctkev_loc = loc
                    , ctkev_rewriters = emptyKiRewriterSet }

newTyCoVar :: AnyPredType -> TcRnIf gbl lcl (TyCoVar (AnyTyVar AnyKiVar) AnyKiVar)
newTyCoVar ty = do
  name <- newSysName (predTypeOccName ty)
  return $ mkLocalTyCoVar name ty

newKiCoVars :: [AnyPredKind] -> TcM [KiCoVar AnyKiVar]
newKiCoVars theta = mapM newKiCoVar theta

newKiCoVar :: AnyPredKind -> TcRnIf gbl lcl (KiCoVar AnyKiVar)
newKiCoVar ki = do
  name <- newSysName (predKindOccName ki)
  return (mkLocalKiCoVar name ki)

-- newWanted :: CtOrigin -> Maybe TypeOrKind -> AnyPredKind -> TcM CtKiEvidence
-- newWanted orig t_or_k predki = do
--   loc <- getCtLocM orig t_or_k
--   newWantedWithLoc loc predki

----------------------------------------------
-- Emitting constraints
----------------------------------------------

{- *********************************************************************
*                                                                      *
        Coercion holes
*                                                                      *
********************************************************************* -}

newTyCoercionHole :: AnyPredType -> TcM AnyTypeCoercionHole
newTyCoercionHole pred_ty = do
  co_var <- newTyCoVar pred_ty
  traceTc "New coercion hole:" (ppr co_var <+> colon <+> ppr pred_ty)
  ref <- newMutVar Nothing
  return $ TypeCoercionHole { tch_co_var = co_var, tch_ref = ref }

newKiCoercionHole
  :: AnyPredKind -> TcM AnyKindCoercionHole
newKiCoercionHole pred_ki = do
  co_var <- newKiCoVar pred_ki
  traceTc "New coercion hole:" (ppr co_var <+> colon <+> ppr pred_ki)
  ref <- newMutVar Nothing
  return $ KindCoercionHole { kch_co_var = co_var, kch_ref = ref }

fillTyCoercionHole :: AnyTypeCoercionHole -> AnyTypeCoercion -> TcM ()
fillTyCoercionHole (TypeCoercionHole { tch_ref = ref, tch_co_var = cv }) co = do
  when debugIsOn $ do
    cts <- readTcRef ref
    whenIsJust cts $ \old_co ->
      pprPanic "Filling a filled coercion hole" (ppr cv $$ ppr co $$ ppr old_co)
  traceTc "Filling coercion hole" (ppr cv <+> text ":=" <+> ppr co)
  writeTcRef ref (Just co)

fillKiCoercionHole
  :: AnyKindCoercionHole
  -> AnyKindCoercion
  -> TcM ()
fillKiCoercionHole (KindCoercionHole { kch_ref = ref, kch_co_var = cv }) co = do
  when debugIsOn $ do
    cts <- readTcRef ref
    whenIsJust cts $ \old_co ->
      pprPanic "Filling a filled coercion hole" (ppr cv $$ ppr co $$ ppr old_co)
  traceTc "Filling coercion hole" (ppr cv <+> text ":=" <+> ppr co)
  writeTcRef ref (Just co)

{- **********************************************************************
*
                      ExpType functions
*
********************************************************************** -}

newInferExpType :: TcM ExpType
newInferExpType = new_inferExpType

new_inferExpType :: TcM ExpType
new_inferExpType = do
  u <- newUnique
  tclvl <- getTcLevel
  traceTc "newInferExpType" (ppr u <+> ppr tclvl)
  ref <- newMutVar Nothing
  return $ Infer $ IR { ir_uniq = u
                      , ir_lvl = tclvl
                      , ir_ref = ref }

readExpType_maybe :: MonadIO m => ExpType -> m (Maybe AnyType)
readExpType_maybe (Check ty) = return (Just ty)
readExpType_maybe (Infer (IR { ir_ref = ref })) = liftIO $ readIORef ref
{-# INLINABLE readExpType_maybe #-}

readExpType :: MonadIO m => ExpType -> m AnyType
readExpType exp_ty = do
  mb_ty <- readExpType_maybe exp_ty
  case mb_ty of
    Just ty -> return ty
    Nothing -> pprPanic "Unknown expected type" (ppr exp_ty)
{-# INLINABLE readExpType #-}

expTypeToType :: ExpType -> TcM AnyType
expTypeToType (Check ty) = return ty
expTypeToType (Infer inf_res) = inferResultToType inf_res

inferResultToType :: InferResult -> TcM AnyType
inferResultToType (IR { ir_uniq = u, ir_lvl = tc_lvl, ir_ref = ref }) = do
  mb_inferred_ty <- readTcRef ref
  tau <- case mb_inferred_ty of
    Just ty -> do ensureMonoType ty
                  return ty
    Nothing -> do tau <- new_meta
                  writeMutVar ref (Just tau)
                  return tau
  traceTc "Forcing ExpType to be monomorphic:"
    (ppr u <+> text ":=" <+> ppr tau)
  return tau
  where
    new_meta = do
      ki <- newMetaKiVarKiAtLevel tc_lvl
      newMetaTyVarTyAtLevel tc_lvl ki

tcInfer :: (ExpSigmaType -> TcM a) -> TcM (a, AnySigmaType)
tcInfer tc_check = do
  res_ty <- new_inferExpType
  result <- tc_check res_ty
  res_ty <- readExpType res_ty
  return (result, res_ty)

{- *********************************************************************
*                                                                      *
              Promoting types
*                                                                      *
********************************************************************* -}

ensureMonoType :: AnyType -> TcM ()
ensureMonoType res_ty
  | isTauTy res_ty
  = return ()
  | otherwise
  = panic "ensureMonoType"

promoteTcType :: TcLevel -> AnyType -> TcM (AnyTypeCoercion, AnyType)
promoteTcType dest_lvl ty = do
  cur_lvl <- getTcLevel
  if cur_lvl `sameDepthAs` dest_lvl
    then return (mkReflTyCo ty, ty)
    else promote_it
  where
    promote_it :: TcM (AnyTypeCoercion, AnyType)
    promote_it = do
      ki <- newMetaKiVarKiAtLevel dest_lvl
      prom_ty <- newMetaTyVarTyAtLevel dest_lvl ki
      co <- unifyInvisibleType ty prom_ty
      return (co, prom_ty)

{- *********************************************************************
*                                                                      *
        Constraints
*                                                                      *
********************************************************************* -}

newImplication :: Implic impl => TcM impl
newImplication = do
  env <- getLclEnv
  warn_inaccessible <- woptM Opt_WarnInaccessibleCode
  return $ setWarnInaccessible warn_inaccessible (implicationPrototype (mkCtLocEnv env))

{- *********************************************************************
*                                                                      *
        MetaTvs
*                                                                      *
********************************************************************* -}

newMetaTyVarName :: FastString -> TcM Name
newMetaTyVarName str = newSysName (mkTyVarOccFS str)

cloneMetaTyVarName :: Name -> TcM Name
cloneMetaTyVarName name = newSysName (nameOccName name)

metaInfoToTyVarName :: MetaInfo -> FastString
metaInfoToTyVarName mi = case mi of
  TauVar -> fsLit "t"
  VarVar -> fsLit "a"

newAnonMetaTyVar :: MetaInfo -> TcMonoKind -> TcM (TcTyVar TcKiVar)
newAnonMetaTyVar mi = newNamedAnonMetaTyVar (metaInfoToTyVarName mi) mi

newNamedAnonMetaTyVar :: FastString -> MetaInfo -> TcMonoKind -> TcM (TcTyVar TcKiVar)
newNamedAnonMetaTyVar tv_name mi kind = do
  name <- newMetaTyVarName tv_name
  details <- newMetaDetails mi
  let tyvar = mkTcTyVar name kind details
  traceTc "newAnonMetaTyVar" (ppr tyvar)
  return tyvar

newPatTyVar :: Name -> AnyMonoKind -> TcM (TcTyVar AnyKiVar)
newPatTyVar name kind = do
  details <- newMetaDetails TauVar
  uniq <- newUnique
  let name' = name `setNameUnique` uniq
      tyvar = mkTcTyVar name' kind details
  traceTc "newPatTyVar" (ppr tyvar)
  return tyvar

cloneAnonMetaTyVar :: MetaInfo -> AnyTyVar AnyKiVar -> AnyMonoKind -> TcM (AnyTyVar AnyKiVar)
cloneAnonMetaTyVar info tv kind = do
  details <- newMetaDetails info
  name <- cloneMetaTyVarName (varName tv)
  let tyvar = toAnyTyVar $ mkTcTyVar name kind details
  traceTc "cloneAnonMetaTyVar" (ppr tyvar <+> colon <+> ppr (varKind tyvar))
  return tyvar

isFilledMetaTyVar_maybe :: TcTyVar AnyKiVar -> TcM (Maybe AnyType)
isFilledMetaTyVar_maybe tv
  -- | isTcTyVar tv
  | MetaVar { mv_ref = ref } <- tcVarDetails tv
  = do cts <- readTcRef ref
       case cts of
         Indirect ty -> return $ Just ty
         Flexi -> return Nothing
  | otherwise
  = return Nothing

{- *********************************************************************
*                                                                      *
        MetaTvs: TauTvs
*                                                                      *
********************************************************************* -}

newFlexiTyVar :: TcMonoKind -> TcM (TcTyVar TcKiVar)
newFlexiTyVar kind = newAnonMetaTyVar TauVar kind

newOpenFlexiTyVarTy :: TcM (Type (TcTyVar TcKiVar) TcKiVar)
newOpenFlexiTyVarTy = do
  tv <- newOpenFlexiTyVar
  return $ mkTyVarTy tv

newOpenFlexiTyVar :: TcM (TcTyVar TcKiVar)
newOpenFlexiTyVar = do
  kind <- newOpenTypeKind
  newFlexiTyVar kind

newMetaTyKiVars :: ([KiVar], [TyVar KiVar]) -> TcM (AnyTvSubst, [AnyKiVar], [AnyTyVar AnyKiVar])
newMetaTyKiVars (kvs, tvs)
  = newMetaTyKiVarsX emptyTvSubst (toAnyKiVar <$> kvs) (asAnyKi . toAnyTyVar <$> tvs)

newMetaTyKiVarsX
  :: AnyTvSubst
  -> [AnyKiVar]
  -> [AnyTyVar AnyKiVar]
  -> TcM (AnyTvSubst, [AnyKiVar], [AnyTyVar AnyKiVar])
newMetaTyKiVarsX (TvSubst is tvset kvsubst) kvs tvs = do
  (kvsubst', kvs) <- mapAccumLM newMetaKiVarX kvsubst kvs
  (tvsubst', tvs) <- mapAccumLM newMetaTyVarX (TvSubst is tvset kvsubst') tvs
  return (tvsubst', kvs, tvs)

newMetaTyVarX :: AnyTvSubst -> AnyTyVar AnyKiVar -> TcM (AnyTvSubst, AnyTyVar AnyKiVar)
newMetaTyVarX = new_meta_tv_x TauVar

new_meta_tv_x
  :: MetaInfo -> AnyTvSubst -> AnyTyVar AnyKiVar -> TcM (AnyTvSubst, AnyTyVar AnyKiVar)
new_meta_tv_x info subst@(TvSubst _ _ kvsubst) tv = do
  new_tv <- cloneAnonMetaTyVar info tv (substMonoKi kvsubst (varKind tv))
  let subst1 = extendTvSubstWithClone subst tv new_tv
  return (subst1, new_tv)

newMetaTyVarTyAtLevel :: TcLevel -> AnyMonoKind -> TcM AnyType
newMetaTyVarTyAtLevel tc_lvl kind = do
  details <- newTauVarDetailsAtLevel tc_lvl
  name <- newMetaTyVarName (fsLit "p")
  return $ mkTyVarTy $ toAnyTyVar $ mkTcTyVar name kind details

{- *********************************************************************
*                                                                      *
        MetaKvs
*                                                                      *
********************************************************************* -}

newMetaKiVarName :: FastString -> TcM Name
newMetaKiVarName str = newSysName (mkKiVarOccFS str)

cloneMetaKiVarName :: Name -> TcM Name
cloneMetaKiVarName name = newSysName (nameOccName name)

metaInfoToKiVarName :: MetaInfo -> FastString
metaInfoToKiVarName meta_info = case meta_info of
  TauVar -> fsLit "kt"
  VarVar -> fsLit "k"

newAnonMetaKiVar :: MetaInfo -> TcM TcKiVar
newAnonMetaKiVar mi = newNamedAnonMetaKiVar (metaInfoToKiVarName mi) mi

newNamedAnonMetaKiVar :: FastString -> MetaInfo -> TcM TcKiVar
newNamedAnonMetaKiVar kivar_name meta_info = do
  name <- newMetaKiVarName kivar_name
  details <- newMetaDetails meta_info
  let kivar = mkTcKiVar name details
  traceTc "newAnonMetaKiVar" (ppr kivar)
  return kivar

newMetaDetails :: MetaInfo -> TcM (TcVarDetails tk)
newMetaDetails info = do
  ref <- newMutVar Flexi
  tclvl <- getTcLevel
  return $ MetaVar { mv_info = info
                   , mv_ref = ref
                   , mv_tclvl = tclvl }

newTauVarDetailsAtLevel :: TcLevel -> TcM (TcVarDetails tk)
newTauVarDetailsAtLevel tclvl = do
  ref <- newMutVar Flexi
  return $ MetaVar { mv_info = TauVar
                   , mv_ref = ref
                   , mv_tclvl = tclvl }

cloneMetaKiVar :: TcKiVar -> TcM TcKiVar
cloneMetaKiVar kv = {-assert (isTcKiVar kv) $ -}do
  ref <- newMutVar Flexi
  name' <- cloneMetaKiVarName (varName kv)
  let details' = case tcVarDetails kv of
                   details@(MetaVar {}) -> details { mv_ref = ref }
                   _ -> pprPanic "cloneMetaKiVar" (ppr kv)
      kivar = mkTcKiVar name' details'
  traceTc "cloneMetaKiVar" (ppr kivar)
  return kivar

cloneMetaKiVarWithInfo :: MetaInfo -> TcLevel -> TcKiVar -> TcM TcKiVar
cloneMetaKiVarWithInfo info tc_lvl kv = do
  ref <- newMutVar Flexi
  name' <- cloneMetaKiVarName (varName kv)
  let details = MetaVar { mv_info = info
                        , mv_ref = ref
                        , mv_tclvl = tc_lvl }
      kivar = mkTcKiVar name' details
  traceTc "cloneMetaKiVarWithInfo" (ppr kivar)
  return kivar

cloneMetaTyVarWithInfo :: MetaInfo -> TcLevel -> TcTyVar AnyKiVar -> TcM (TcTyVar AnyKiVar)
cloneMetaTyVarWithInfo info tc_lvl tv = do
  ref <- newMutVar Flexi
  name' <- cloneMetaTyVarName (varName tv)
  let details = MetaVar { mv_info = info
                        , mv_ref = ref
                        , mv_tclvl = tc_lvl }
      tyvar = mkTcTyVar name' (varKind tv) details
  traceTc "cloneMetaTyVarWithInfo" (ppr tyvar)
  return tyvar

readMetaTyVar :: (MonadIO m, Outputable kv) => TcTyVar kv -> m (MetaDetails AnyType)
readMetaTyVar tyvar = assertPpr (isMetaVar tyvar) (ppr tyvar)
  $ liftIO $ readIORef (metaVarRef tyvar)
{-# SPECIALIZE readMetaTyVar :: TcTyVar TcKiVar -> TcM (MetaDetails AnyType) #-}
{-# SPECIALIZE readMetaTyVar :: TcTyVar TcKiVar -> ZonkM (MetaDetails AnyType) #-}
{-# SPECIALIZE readMetaTyVar :: TcTyVar AnyKiVar -> TcM (MetaDetails AnyType) #-}
{-# SPECIALIZE readMetaTyVar :: TcTyVar AnyKiVar -> ZonkM (MetaDetails AnyType) #-}

readMetaKiVar :: MonadIO m => TcKiVar -> m (MetaDetails AnyMonoKind)
readMetaKiVar kivar = assertPpr (isMetaVar kivar) (ppr kivar)
  $ liftIO $ readIORef (metaVarRef kivar)
{-# SPECIALIZE readMetaKiVar :: TcKiVar -> TcM (MetaDetails AnyMonoKind) #-}
{-# SPECIALIZE readMetaKiVar :: TcKiVar -> ZonkM (MetaDetails AnyMonoKind) #-}

isFilledMetaKiVar_maybe :: TcKiVar -> TcM (Maybe AnyMonoKind)
isFilledMetaKiVar_maybe kv
  | MetaVar { mv_ref = ref } <- tcVarDetails kv
  = do cts <- readTcRef ref
       case cts of
         Indirect ki -> return $ Just ki
         Flexi -> return Nothing
  | otherwise
  = return Nothing

{- *********************************************************************
*                                                                      *
        MetaKvs (meta kind variables; mutable)
*                                                                      *
********************************************************************* -}

newPatKiVar :: Name -> TcM TcKiVar
newPatKiVar name = do
  details <- newMetaDetails TauVar
  uniq <- newUnique
  let name' = name `setNameUnique` uniq
      kivar = mkTcKiVar name details
  traceTc "newPatKiVar" (ppr kivar)
  return kivar

cloneAnonMetaKiVar :: MetaInfo -> AnyKiVar -> TcM TcKiVar
cloneAnonMetaKiVar info kv = do
  details <- newMetaDetails info
  name <- cloneMetaKiVarName (varName kv)
  let kivar = mkTcKiVar name details
  traceTc "cloneAnonMetaKiVar" (ppr kivar)
  return kivar

{- *********************************************************************
*                                                                      *
        MetaKvs: TauKvs
*                                                                      *
********************************************************************* -}

newOpenTypeKind :: TcM TcMonoKind
newOpenTypeKind = newFlexiKiVarKi

newFlexiKiVar :: TcM TcKiVar
newFlexiKiVar = newAnonMetaKiVar TauVar

newFlexiKiVarKi :: TcM TcMonoKind
newFlexiKiVarKi = do
  tc_kivar <- newFlexiKiVar
  return $ mkKiVarKi tc_kivar

newMetaKiVarX :: KvSubst AnyKiVar -> AnyKiVar -> TcM (KvSubst AnyKiVar, AnyKiVar)
newMetaKiVarX = new_meta_kv_x TauVar

new_meta_kv_x :: MetaInfo -> KvSubst AnyKiVar -> AnyKiVar -> TcM (KvSubst AnyKiVar, AnyKiVar)
new_meta_kv_x info subst kv = do
  new_kv <- toAnyKiVar <$> cloneAnonMetaKiVar info kv
  let subst1 = extendKvSubstWithClone subst kv new_kv
  return (subst1, new_kv)

newMetaKiVarKiAtLevel :: TcLevel -> TcM AnyMonoKind
newMetaKiVarKiAtLevel tc_lvl = do
  details <- newTauVarDetailsAtLevel tc_lvl
  name <- newMetaKiVarName (fsLit "pk")
  return $ mkKiVarKi $ toAnyKiVar $ mkTcKiVar name details

{- *********************************************************************
*                                                                      *
             Finding variables to quantify over
*                                                                      *
********************************************************************* -}

candidateQTyKiVarsOfTypes :: [AnyType] -> TcM (DTcKiVarSet, DTcTyVarSet)
candidateQTyKiVarsOfTypes tys = do
  cur_lvl <- getTcLevel
  foldlM (\acc ty -> collect_cand_qtkvs ty cur_lvl (emptyVarSet, emptyVarSet) acc ty)
         (emptyDVarSet, emptyDVarSet) tys

collect_cand_qtkvs
  :: AnyType
  -> TcLevel
  -> (AnyKiVarSet, AnyTyVarSet AnyKiVar)
  -> (DTcKiVarSet, DTcTyVarSet)
  -> AnyType
  -> TcM (DTcKiVarSet, DTcTyVarSet)
collect_cand_qtkvs orig_ty cur_lvl (boundkvs, boundtvs) dvs ty = go dvs ty
  where
    is_bound_kv kv = kv `elemVarSet` boundkvs
    is_bound_tv tv = tv `elemVarSet` boundtvs

    go :: (DTcKiVarSet, DTcTyVarSet) -> AnyType -> TcM (DTcKiVarSet, DTcTyVarSet)
    go dv (AppTy t1 t2) = foldlM go dv [t1, t2]
    go dv (TyConApp _ tys) = foldlM go dv tys
    go (dkv, dtv) (FunTy ki arg res) = do
      dkv1 <- collect_cand_qkvs (Mono ki) cur_lvl boundkvs dkv (Mono ki)
      foldlM go (dkv1, dtv) [arg, res]
    go dv (TyVarTy tv)
      | is_bound_tv tv = return dv
      | otherwise = do m_contents <- handleAnyTv (const (return Nothing))
                                     isFilledMetaTyVar_maybe tv
                       case m_contents of
                         Just ind_ty -> go dv ind_ty
                         Nothing -> go_tv dv tv
    go (dkv, dtv) (ForAllTy (Bndr tv _) ty) = do
      dkv1 <- collect_cand_qkvs (Mono $ varKind tv) cur_lvl boundkvs dkv (Mono $ varKind tv)
      collect_cand_qtkvs orig_ty cur_lvl (boundkvs, boundtvs `extendVarSet` tv) (dkv1, dtv) ty

    go (dkv, dtv) (TyLamTy tv ty) = do
      dkv1 <- collect_cand_qkvs (Mono $ varKind tv) cur_lvl boundkvs dkv (Mono $ varKind tv)
      collect_cand_qtkvs orig_ty cur_lvl (boundkvs, boundtvs `extendVarSet` tv) (dkv1, dtv) ty

    go dv (BigTyLamTy kv ty) = 
      collect_cand_qtkvs orig_ty cur_lvl (boundkvs `extendVarSet` kv, boundtvs) dv ty

    go dv (CastTy ty co) = do
      (dkv1, dtv1) <- go dv ty
      dkv2 <- collect_cand_qkvs_co co cur_lvl (boundtvs, boundkvs) dkv1 co
      return (dkv2, dtv1)

    go (dkv, dtv) (Embed ki) = do
      dkv1 <- collect_cand_qkvs (Mono ki) cur_lvl boundkvs dkv (Mono ki)
      return (dkv1, dtv)

    go (dkv, dtv) (KindCoercion co) = do
      dkv1 <- collect_cand_qkvs_co co cur_lvl (boundtvs, boundkvs) dkv co
      return (dkv1, dtv)

    go _ other = pprPanic "collect_cand_qkvs_ty" (ppr other)

    go_tv :: (DTcKiVarSet, DTcTyVarSet) -> AnyTyVar AnyKiVar -> TcM (DTcKiVarSet, DTcTyVarSet)
    go_tv dv@(dkv, dtv) tv
      | cur_lvl `deeperThanOrSame` handleAnyTv (const topTcLevel) varLevel tv
      = return dv
      | handleAnyTv (const False) (\tv -> case tcVarDetails tv of
          SkolemVar _ lvl -> lvl `strictlyDeeperThan` pushTcLevel cur_lvl
          _ -> False) tv
      = return dv
      | handleAnyTv (const False) (\tv -> tv `elemDVarSet` dtv) tv
      = return dv
      | otherwise
      = do tv_kind <- liftZonkM $ zonkTcMonoKind (varKind tv)
           let tv_kind_vars = varsOfMonoKind tv_kind
           if intersectsVarSet boundkvs tv_kind_vars
             then pprPanic "Naughty quantifier"
                  $ vcat [ ppr tv <+> colon <+> ppr tv_kind
                         , ppr boundkvs, ppr tv_kind_vars ]
             else do dkv1 <- collect_cand_qkvs (Mono tv_kind) cur_lvl boundkvs dkv (Mono tv_kind)
                     return (dkv1, dtv)

candidateQKiVarsOfType :: AnyType -> TcM DTcKiVarSet
candidateQKiVarsOfType ty = do
  cur_lvl <- getTcLevel
  collect_cand_qkvs_ty ty cur_lvl (emptyVarSet, emptyVarSet) emptyDVarSet ty

collect_cand_qkvs_ty
  :: AnyType
  -> TcLevel
  -> (AnyTyVarSet AnyKiVar, AnyKiVarSet)
  -> DTcKiVarSet
  -> AnyType
  -> TcM DTcKiVarSet
collect_cand_qkvs_ty orig_ty cur_lvl (boundtvs, boundkvs) dvs ty = go dvs ty
  where
    is_bound tv = tv `elemVarSet` boundtvs

    go :: DTcKiVarSet -> AnyType -> TcM DTcKiVarSet
    go dv (AppTy t1 t2) = foldlM go dv [t1, t2]
    go dv (TyConApp _ tys) = foldlM go dv tys
    go dv (FunTy ki arg res) = do
      dv1 <- collect_cand_qkvs (Mono ki) cur_lvl boundkvs dv (Mono ki)
      foldlM go dv1 [arg, res]
    go dv (TyVarTy tv)
      | is_bound tv = return dv
      | otherwise = do m_contents <- handleAnyTv (const (return Nothing))
                                     isFilledMetaTyVar_maybe tv
                       case m_contents of
                         Just ind_ty -> go dv ind_ty
                         Nothing -> go_tv dv tv
    go dv (ForAllTy (Bndr tv _) ty) = do
      dv1 <- collect_cand_qkvs (Mono $ varKind tv) cur_lvl boundkvs dv (Mono $ varKind tv)
      collect_cand_qkvs_ty orig_ty cur_lvl (boundtvs `extendVarSet` tv, boundkvs) dv1 ty

    go dv (TyLamTy tv ty) = do
      dv1 <- collect_cand_qkvs (Mono $ varKind tv) cur_lvl boundkvs dv (Mono $ varKind tv)
      collect_cand_qkvs_ty orig_ty cur_lvl (boundtvs `extendVarSet` tv, boundkvs) dv1 ty

    go dv (BigTyLamTy kv ty) = 
      collect_cand_qkvs_ty orig_ty cur_lvl (boundtvs, boundkvs `extendVarSet` kv) dv ty

    go dv (CastTy ty co) = do
      dv1 <- go dv ty
      collect_cand_qkvs_co co cur_lvl (boundtvs, boundkvs) dv co

    go dv (Embed ki) = collect_cand_qkvs (Mono ki) cur_lvl boundkvs dv (Mono ki)

    go dv (KindCoercion co) = collect_cand_qkvs_co co cur_lvl (boundtvs, boundkvs) dv co

    go _ other = pprPanic "collect_cand_qkvs_ty" (ppr other)

    go_tv :: DTcKiVarSet -> AnyTyVar AnyKiVar -> TcM DTcKiVarSet
    go_tv dv tv
      | cur_lvl `deeperThanOrSame` handleAnyTv (const topTcLevel) varLevel tv
      = return dv
      | handleAnyTv (const False) (\tv -> case tcVarDetails tv of
          SkolemVar _ lvl -> lvl `strictlyDeeperThan` pushTcLevel cur_lvl
          _ -> False) tv
      = return dv
      | otherwise
      = do tv_kind <- liftZonkM $ zonkTcMonoKind (varKind tv)
           collect_cand_qkvs (Mono tv_kind) cur_lvl boundkvs dv (Mono tv_kind)

candidateQKiVarsOfKind :: AnyKind -> TcM DTcKiVarSet
candidateQKiVarsOfKind ki = do
  cur_lvl <- getTcLevel
  collect_cand_qkvs ki cur_lvl emptyVarSet emptyDVarSet ki

collect_cand_qkvs
  :: AnyKind
  -> TcLevel
  -> AnyKiVarSet
  -> DTcKiVarSet
  -> AnyKind
  -> TcM DTcKiVarSet
collect_cand_qkvs orig_ki cur_lvl bound dvs ki = go dvs ki
  where
    is_bound kv = kv `elemVarSet` bound

    -----------------
    go :: DTcKiVarSet -> AnyKind -> TcM DTcKiVarSet
    go dv (Mono ki) = go_mono dv ki
    go dv (ForAllKi kv ki) = collect_cand_qkvs orig_ki cur_lvl (bound `extendVarSet` kv) dv ki

    go_mono :: DTcKiVarSet -> AnyMonoKind -> TcM DTcKiVarSet
    go_mono dv (KiPredApp _ k1 k2) = foldlM go_mono dv [k1, k2]
    go_mono dv (FunKi _ k1 k2) = foldlM go_mono dv [k1, k2]
    go_mono dv (BIKi {}) = return dv
    go_mono dv (KiVarKi kv)
      | is_bound kv = return dv
      | Just kv <- toTcKiVar_maybe kv
      = do m_contents <- isFilledMetaKiVar_maybe kv
           case m_contents of
             Just ind_ki -> go_mono dv ind_ki
             Nothing -> go_kv dv kv
      | otherwise
      = pprPanic "collect_cand_qkvs found unbound non-meta kivar"
        (ppr orig_ki $$ ppr kv $$ ppr bound)

    go_kv :: DTcKiVarSet -> TcKiVar -> TcM DTcKiVarSet
    go_kv dv kv
      | cur_lvl `deeperThanOrSame` varLevel kv
      = return dv
      | case tcVarDetails kv of
          SkolemVar _ lvl -> lvl `strictlyDeeperThan` pushTcLevel cur_lvl
          _ -> False
      = return dv
      | kv `elemDVarSet` dv
      = return dv
      | otherwise
      = return $ dv `extendDVarSet` kv

collect_cand_qkvs_co
  :: AnyKindCoercion
  -> TcLevel
  -> (AnyTyVarSet AnyKiVar, AnyKiVarSet)
  -> DTcKiVarSet
  -> AnyKindCoercion
  -> TcM DTcKiVarSet
collect_cand_qkvs_co orig_co cur_lvl (boundtvs, boundkvs) = go_co
  where
    go_co dv (Refl ki) = collect_cand_qkvs (Mono ki) cur_lvl boundkvs dv (Mono ki)
    go_co dv BI_U_A = return dv
    go_co dv BI_A_L = return dv
    go_co dv (BI_U_LTEQ ki) = collect_cand_qkvs (Mono ki) cur_lvl boundkvs dv (Mono ki)
    go_co dv (BI_LTEQ_L ki) = collect_cand_qkvs (Mono ki) cur_lvl boundkvs dv (Mono ki)
    go_co dv (LiftEq co) = go_co dv co
    go_co dv (LiftLT co) = go_co dv co
    go_co dv (FunCo _ _ co1 co2) = foldM go_co dv [co1, co2]

    go_co dv (SymCo co) = go_co dv co
    go_co dv (TransCo co1 co2) = foldM go_co dv [co1, co2]
    go_co dv (SelCo _ co) = go_co dv co

    go_co dv (HoleCo hole) = do
      m_co <- unpackKiCoercionHole_maybe hole
      case m_co of
        Just co -> go_co dv co
        Nothing -> go_cv dv (coHoleCoVar hole)

    go_co dv (KiCoVarCo cv) = go_cv dv cv

    go_cv :: DTcKiVarSet -> KiCoVar AnyKiVar -> TcM DTcKiVarSet
    go_cv dv cv
      | is_bound cv = return dv
      | otherwise = do
          traceTc "COLLECTING KICOVAR" (ppr cv)
          collect_cand_qkvs (Mono $ varKind cv) cur_lvl boundkvs dv (Mono $ varKind cv)

    is_bound :: KiCoVar AnyKiVar -> Bool
    is_bound v = toAnyTyVar v `elemVarSet` boundtvs

{- *********************************************************************
*                                                                      *
             Quantification
*                                                                      *
********************************************************************* -}

quantifyTyKiVars
  :: SkolemInfo
  -> (DTcKiVarSet, DTcTyVarSet)
  -> TcM ([TcKiVar], [TcTyVar AnyKiVar])
quantifyTyKiVars skol_info (dkvs, dtvs)
  | isEmptyDVarSet dtvs
  = do traceTc "quantifyTyKiVars has no tyvars to quantify" empty
       (, []) <$> quantifyKiVars skol_info dkvs
  | otherwise
  = do traceTc "quantifyTyKiVars {"
         $ vcat [ text "dtvs =" <+> ppr dtvs ]
       final_qkvs <- quantifyKiVars skol_info dkvs

       -- We can't default tyvars here (in GHC, the defaulting of tvs is really for non-dep kivars)
       final_qtvs <- liftZonkM $ mapM zonk_quant (dVarSetElems dtvs)

       traceTc "quantifyTyKiVars }"
         $ vcat [ text "final_qtvs:" <+> pprTyVars final_qtvs ]

       let co_vars = filter isKiCoVar final_qtvs
       massertPpr (null co_vars) (ppr co_vars)

       return (final_qkvs, final_qtvs)
  where
    zonk_quant tv = skolemizeQuantifiedTyVar skol_info tv

quantifyKiVars :: SkolemInfo -> DTcKiVarSet -> TcM [TcKiVar]
quantifyKiVars skol_info kvs
  | isEmptyDVarSet kvs
  = do traceTc "quantifyKiVars has nothing to quantify" empty
       return []
  | otherwise
  = do traceTc "quantifyKiVars {"
         $ vcat [ text "kvs =" <+> ppr kvs ]

       final_qkvs <- liftZonkM $ mapM zonk_quant (dVarSetElems kvs)

       traceTc "quantifyKiVars }"
         $ vcat [ text "final_qkvs =" <+> (sep $ map ppr final_qkvs) ]

       return final_qkvs
  where
    zonk_quant kv = skolemizeQuantifiedKiVar skol_info kv

zonkAndSkolemize :: SkolemInfo -> TcKiVar -> ZonkM TcKiVar
zonkAndSkolemize skol_info var
  | isTcVarVar var
  = do zonked_kivar <- zonkTcKiVarToTcKiVar var
       skolemizeQuantifiedKiVar skol_info zonked_kivar
  | otherwise
  = assertPpr (isImmutableVar var) (ppr var)
    $ return var

skolemizeQuantifiedTyVar :: SkolemInfo -> (TcTyVar AnyKiVar) -> ZonkM (TcTyVar AnyKiVar)
skolemizeQuantifiedTyVar skol_info tv
  = case tcVarDetails tv of
      MetaVar {} -> panic "skolemizeUnboundMetaTyVar skol_info tv"
      SkolemVar _ lvl -> do kind <- panic "zonkTcMonoKind (varKind tv)"
                            let details = SkolemVar skol_info lvl
                                name = varName tv
                            return $ mkTcTyVar name kind details

skolemizeQuantifiedKiVar :: SkolemInfo -> TcKiVar -> ZonkM TcKiVar
skolemizeQuantifiedKiVar skol_info kv
  = case tcVarDetails kv of
      MetaVar {} -> skolemizeUnboundMetaKiVar skol_info kv
      SkolemVar _ lvl -> do let details = SkolemVar skol_info lvl
                                name = varName kv
                            return $ mkTcKiVar name details

defaultKiVar :: TcKiVar -> TcM Bool
defaultKiVar kv
  | not (isMetaVar kv)
    || isTcVarVar kv
  = return False
  -- | isConcreteVar kv
  -- = do lvl <- getTcLevel
  --      _ <- promoteMetaKiVarTo lvl kv
  --      return True
  | otherwise
  = return False

defaultKiVars :: DTcKiVarSet -> TcM [TcKiVar]
defaultKiVars dvs = do
  let kvs = dVarSetElems dvs
  defaulted_kvs <- mapM defaultKiVar kvs
  return [ kv | (kv, False) <- kvs `zip` defaulted_kvs ]

skolemizeUnboundMetaTyVar :: SkolemInfo -> TcTyVar AnyKiVar -> ZonkM (TyVar KiVar)
skolemizeUnboundMetaTyVar skol_info tv = assertPpr (isMetaVar tv) (ppr tv) $ do
  check_empty tv
  ZonkGblEnv { zge_src_span = here, zge_tc_level = tc_lvl } <- getZonkGblEnv
  kind <- zonkTcMonoKind (varKind tv)
  let tv_name = varName tv
      final_name | isSystemName tv_name
                 = mkInternalName (nameUnique tv_name) (nameOccName tv_name) here
                 | otherwise
                 = tv_name
      details = SkolemVar skol_info (pushTcLevel tc_lvl)
      final_tv = mkTcTyVar final_name kind details

  traceZonk "Skolemizing" (ppr tv <+> text ":=" <+> ppr final_tv)
  writeMetaTyVar tv (mkTyVarTy (toAnyTyVar final_tv))
  panic "return final_tv"
  where
    check_empty tv = when debugIsOn $ do
      cts <- readMetaTyVar tv
      case cts of
        Flexi -> return ()
        Indirect ty -> warnPprTrace True "skolemizeUnboundMetaTyVar" (ppr tv $$ ppr ty)
                       $ return ()
                   
skolemizeUnboundMetaKiVar :: SkolemInfo -> TcKiVar -> ZonkM TcKiVar
skolemizeUnboundMetaKiVar skol_info kv = assertPpr (isMetaVar kv) (ppr kv) $ do
  check_empty kv
  ZonkGblEnv { zge_src_span = here, zge_tc_level = tc_lvl } <- getZonkGblEnv
  let kv_name = varName kv
      final_name | isSystemName kv_name
                 = mkInternalName (nameUnique kv_name) (nameOccName kv_name) here
                 | otherwise
                 = kv_name
      details = SkolemVar skol_info (pushTcLevel tc_lvl)
      final_kv = mkTcKiVar final_name details

  traceZonk "Skolemizing" (ppr kv <+> text ":=" <+> ppr final_kv)
  writeMetaKiVar kv (mkKiVarKi $ toAnyKiVar final_kv)
  return final_kv
  where
    check_empty kv = when debugIsOn $ do
      cts <- readMetaKiVar kv
      case cts of
        Flexi -> return ()
        Indirect ki -> warnPprTrace True "skolemizeUnboundMetaKiVar" (ppr kv $$ ppr ki)
                       $ return ()

doNotQuantifyKiVars :: DTcKiVarSet -> TcM ()
doNotQuantifyKiVars dvs
  | isEmptyDVarSet dvs
  = traceTc "doNotQuantifyKiVars has nothing" empty
  | otherwise
  = do traceTc "doNotQuantifyKiVars" (ppr dvs)
       undefaulted <- defaultKiVars dvs
       let leftover_metas = filter isMetaVar undefaulted
       massertPpr (null leftover_metas)
         $ vcat [ text "doNotQuantifyKiVars has leftover_metas"
                , ppr leftover_metas ]
       traceTc "doNotQuantifyKiVars success" empty

tcCheckUsage :: Name -> AnyKind -> TcM a -> TcM (a, AnyCsWrapper)
tcCheckUsage name id_kind thing_inside = do
  (local_usage, result) <- tcCollectingUsage thing_inside
  wrapper <- check_then_add_usage local_usage
  return (result, wrapper)
  where
    check_then_add_usage :: UsageEnv -> TcM AnyCsWrapper
    check_then_add_usage uenv = do
      let actual_u = lookupUE uenv name
      traceTc "check_then_add_usage" (ppr id_kind $$ ppr actual_u)
      wrapper <- tcSubMult (UsageEnvironmentOf name) (usageToKind actual_u) id_kind
      tcEmitBindingUsage (deleteUE uenv name)
      return wrapper

usageToKind :: Usage -> BuiltInKi
usageToKind Zero = AKd
usageToKind One = LKd
usageToKind Many = UKd

{- *********************************************************************
*                                                                      *
              Promotion
*                                                                      *
********************************************************************* -}

promoteMetaKiVarTo :: HasDebugCallStack => TcLevel -> TcKiVar -> TcM Bool
promoteMetaKiVarTo tclvl kv
  | assertPpr (isMetaVar kv) (ppr kv)
    $ varLevel kv `strictlyDeeperThan` tclvl
  = do cloned_kv <- cloneMetaKiVar kv
       let rhs_kv = setMetaVarTcLevel cloned_kv tclvl
       liftZonkM $ panic "writeMetaKiVar kv (mkKiVarKi rhs_kv)"
       traceTc "promoteKiVar" (ppr kv <+> text "-->" <+> ppr rhs_kv)
       return True
  | otherwise
  = return False

promoteKiVarSet :: HasDebugCallStack => TcKiVarSet -> TcM Bool
promoteKiVarSet kvs = do
  tclvl <- getTcLevel
  bools <- mapM (promoteMetaKiVarTo tclvl)
           $ filter isPromotableMetaVar
           $ nonDetEltsUniqSet kvs
  return $ or bools

promoteAnyKiVarSet :: AnyKiVarSet -> TcM Bool
promoteAnyKiVarSet kvs = do
  tclvl <- getTcLevel
  bools <- mapM (handleAnyKv
                 (const $ return False)
                 (promoteMetaKiVarTo tclvl))
           $ filter (handleAnyKv (const False) isPromotableMetaVar)
           $ nonDetEltsUniqSet kvs
  return $ or bools
