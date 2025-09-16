module CSlash.Tc.Utils.TcMType where

import CSlash.Cs
import CSlash.Platform

import CSlash.Driver.DynFlags

import {-# SOURCE #-} CSlash.Tc.Utils.Unify ( tcSubMult )
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
import CSlash.Core.Type.Rep
import CSlash.Core.Type.Ppr
import CSlash.Core.Type.Ppr
import CSlash.Core.Type.Subst
import CSlash.Core.Kind
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

newWanted :: CtOrigin -> Maybe TypeOrKind -> AnyPredKind -> TcM CtKiEvidence
newWanted orig t_or_k predki = do
  loc <- getCtLocM orig t_or_k
  newWantedWithLoc loc predki

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

readExpType_maybe :: MonadIO m => ExpType -> m (Maybe AnyType)
readExpType_maybe (Check ty) = return (Just ty)
readExpType_maybe (Infer _) = return Nothing
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
expTypeToType (Infer _) = panic "expTypeToType"

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

newMetaTyVarX :: AnyTvSubst -> AnyTyVar AnyKiVar -> TcM (AnyTvSubst, AnyTyVar AnyKiVar)
newMetaTyVarX = new_meta_tv_x TauVar

new_meta_tv_x
  :: MetaInfo -> AnyTvSubst -> AnyTyVar AnyKiVar -> TcM (AnyTvSubst, AnyTyVar AnyKiVar)
new_meta_tv_x info subst@(TvSubst _ _ kvsubst) tv = do
  new_tv <- cloneAnonMetaTyVar info tv (substMonoKi kvsubst (varKind tv))
  let subst1 = extendTvSubstWithClone subst tv new_tv
  return (subst1, new_tv)

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

-- newMetaDetailsK :: MetaInfoK -> TcM TcKiVarDetails
-- newMetaDetailsK info = do
--   ref <- newMutVar Flexi
--   tclvl <- getTcLevel
--   return (MetaKv { mkv_info = info, mkv_ref = ref, mkv_tclvl = tclvl })

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

{- *********************************************************************
*                                                                      *
             Finding variables to quantify over
*                                                                      *
********************************************************************* -}

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
      dv1 <- collect_cand_qkvs (Mono ki) cur_lvl boundkvs dvs (Mono ki)
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

    go dv (KindCoercion co) = collect_cand_qkvs_co co cur_lvl (boundtvs, boundkvs) dvs co

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

skolemizeQuantifiedTyVar :: SkolemInfo -> (TcTyVar TcKiVar) -> ZonkM (TcTyVar TcKiVar)
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
