module CSlash.Tc.Utils.TcMType where

import CSlash.Cs
import CSlash.Platform

import CSlash.Driver.DynFlags

-- import {-# SOURCE #-} GHC.Tc.Utils.Unify( unifyInvisibleType, tcSubMult )
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.Constraint
-- import GHC.Tc.Types.Evidence
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
import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Core.TyCon
-- import GHC.Core.Coercion
-- import GHC.Core.Class
import CSlash.Core.Predicate
import CSlash.Core.UsageEnv

import CSlash.Types.Var
import CSlash.Types.Id as Id
import CSlash.Types.Name
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
  details <- newMetaDetailsK TauKv
  name <- newMetaKiVarName (fsLit "k")
  let kv = mkTcKiVar name details
  traceTc "newMetaKindVar" (ppr kv)
  return (mkKiVarMKi kv)

{- **********************************************************************
*                                                                       *
            Evidence variables
*                                                                       *
********************************************************************** -}

newKiEvVar :: TcPredKind -> TcRnIf gbl lcl KiEvVar
newKiEvVar ki = do
  name <- newSysName (predKindOccName ki)
  return $ mkKiCoVar name ki

predKindOccName :: PredKind -> OccName
predKindOccName ki = case classifyPredKind ki of
  EqPred {} -> mkVarOccFS (fsLit "co")
  IrredPred {} -> mkVarOccFS (fsLit "irred")
  RelPred {} -> mkVarOccFS (fsLit "relco")

{- *********************************************************************
*                                                                      *
        Coercion holes
*                                                                      *
********************************************************************* -}

newKiCoercionHole :: TcPredKind -> TcM KindCoercionHole
newKiCoercionHole pred_ki = do
  co_var <- newKiEvVar pred_ki
  traceTc "New coercion hole:" (ppr co_var <+> colon <+> ppr pred_ki)
  ref <- newMutVar Nothing
  return $ CoercionHole { ch_co_var = co_var, ch_ref = ref }

fillKiCoercionHole :: KindCoercionHole -> KindCoercion -> TcM ()
fillKiCoercionHole (CoercionHole { ch_ref = ref, ch_co_var = cv }) co = do
  when debugIsOn $ do
    cts <- readTcRef ref
    whenIsJust cts $ \old_co ->
      pprPanic "Filling a filled coercion hole" (ppr cv $$ ppr co $$ ppr old_co)
  traceTc "Filling coercion hole" (ppr cv <+> text ":=" <+> ppr co)
  writeTcRef ref (Just co)

{- *********************************************************************
*                                                                      *
        Constraints
*                                                                      *
********************************************************************* -}

newImplication :: TcM Implication
newImplication = do
  env <- getLclEnv
  warn_inaccessible <- woptM Opt_WarnInaccessibleCode
  return $ (implicationPrototype (mkCtLocEnv env))
           { ic_warn_inaccessible = warn_inaccessible }

{- *********************************************************************
*                                                                      *
        MetaKvs
*                                                                      *
********************************************************************* -}

isFilledMetaTyVar_maybe :: TcTyVar -> TcM (Maybe Type)
isFilledMetaTyVar_maybe tv
  | isTcTyVar tv
  , MetaTv { mtv_ref = ref } <- tcTyVarDetails tv
  = do cts <- readTcRef ref
       case cts of
         Indirect ty -> return $ Just ty
         Flexi -> return Nothing
  | otherwise
  = return Nothing

{- *********************************************************************
*                                                                      *
        MetaKvs
*                                                                      *
********************************************************************* -}

newMetaKiVarName :: FastString -> TcM Name
newMetaKiVarName str = newSysName (mkKiVarOccFS str)

cloneMetaKiVarName :: Name -> TcM Name
cloneMetaKiVarName name = newSysName (nameOccName name)

metaInfoToKiVarName :: MetaInfoK -> FastString
metaInfoToKiVarName meta_info = case meta_info of
  TauKv -> fsLit "kt"
  KiVarKv -> fsLit "k"

newAnonMetaKiVar :: MetaInfoK -> TcM TcKiVar
newAnonMetaKiVar mi = newNamedAnonMetaKiVar (metaInfoToKiVarName mi) mi

newNamedAnonMetaKiVar :: FastString -> MetaInfoK -> TcM TcKiVar
newNamedAnonMetaKiVar kivar_name meta_info = do
  name <- newMetaKiVarName kivar_name
  details <- newMetaDetailsK meta_info
  let kivar = mkTcKiVar name details
  traceTc "newAnonMetaKiVar" (ppr kivar)
  return kivar

newMetaDetails :: MetaInfo -> TcM TcTyVarDetails
newMetaDetails info = do
  ref <- newMutVar Flexi
  tclvl <- getTcLevel
  return $ MetaTv { mtv_info = info
                  , mtv_ref = ref
                  , mtv_tclvl = tclvl }

newMetaDetailsK :: MetaInfoK -> TcM TcKiVarDetails
newMetaDetailsK info = do
  ref <- newMutVar Flexi
  tclvl <- getTcLevel
  return (MetaKv { mkv_info = info, mkv_ref = ref, mkv_tclvl = tclvl })

cloneMetaKiVar :: TcKiVar -> TcM TcKiVar
cloneMetaKiVar kv = assert (isTcKiVar kv) $ do
  ref <- newMutVar Flexi
  name' <- cloneMetaKiVarName (kiVarName kv)
  let details' = case tcKiVarDetails kv of
                   details@(MetaKv {}) -> details { mkv_ref = ref }
                   _ -> pprPanic "cloneMetaKiVar" (ppr kv)
      kivar = mkTcKiVar name' details'
  traceTc "cloneMetaKiVar" (ppr kivar)
  return kivar

cloneMetaKiVarWithInfo :: MetaInfoK -> TcLevel -> TcKiVar -> TcM TcKiVar
cloneMetaKiVarWithInfo info tc_lvl kv = assert (isTcKiVar kv) $ do
  ref <- newMutVar Flexi
  name' <- cloneMetaKiVarName (kiVarName kv)
  let details = MetaKv { mkv_info = info
                       , mkv_ref = ref
                       , mkv_tclvl = tc_lvl }
      kivar = mkTcKiVar name' details
  traceTc "cloneMetaKiVarWithInfo" (ppr kivar)
  return kivar

readMetaTyVar :: MonadIO m => TypeVar -> m MetaDetails
readMetaTyVar tyvar = assertPpr (isMetaTyVar tyvar) (ppr tyvar)
  $ liftIO $ readIORef (metaTyVarRef tyvar)
{-# SPECIALIZE readMetaTyVar :: TypeVar -> TcM MetaDetails #-}
{-# SPECIALIZE readMetaTyVar :: TypeVar -> ZonkM MetaDetails #-}

readMetaKiVar :: MonadIO m => KindVar -> m MetaDetailsK
readMetaKiVar kivar = assertPpr (isMetaKiVar kivar) (ppr kivar)
  $ liftIO $ readIORef (metaKiVarRef kivar)
{-# SPECIALIZE readMetaKiVar :: KindVar -> TcM MetaDetailsK #-}
{-# SPECIALIZE readMetaKiVar :: KindVar -> ZonkM MetaDetailsK #-}

isFilledMetaKiVar_maybe :: TcKiVar -> TcM (Maybe MonoKind)
isFilledMetaKiVar_maybe kv
  | isTcKiVar kv
  , MetaKv { mkv_ref = ref } <- tcKiVarDetails kv
  = do cts <- readTcRef ref
       case cts of
         Indirect ki -> return $ Just ki
         Flexi -> return Nothing
  | otherwise
  = return Nothing

{- *********************************************************************
*                                                                      *
        MetaKvs: TauKvs
*                                                                      *
********************************************************************* -}

newOpenTypeKind :: TcM TcMonoKind
newOpenTypeKind = newFlexiKiVarKi

newFlexiKiVar :: TcM TcKiVar
newFlexiKiVar = newAnonMetaKiVar TauKv

newFlexiKiVarKi :: TcM TcMonoKind
newFlexiKiVarKi = do
  tc_kivar <- newFlexiKiVar
  return $ mkKiVarMKi tc_kivar

{- *********************************************************************
*                                                                      *
             Finding variables to quantify over
*                                                                      *
********************************************************************* -}

candidateQKiVarsOfType :: TcType -> TcM DKiVarSet
candidateQKiVarsOfType ty = do
  cur_lvl <- getTcLevel
  collect_cand_qkvs_ty ty cur_lvl emptyVarSet emptyDVarSet ty

collect_cand_qkvs_ty :: TcType -> TcLevel -> VarSet -> DKiVarSet -> Type -> TcM DKiVarSet
collect_cand_qkvs_ty orig_ty cur_lvl bound dvs ty = go dvs ty
  where
    is_bound kv = kv `elemVarSet` bound

    go :: DKiVarSet -> TcType -> TcM DKiVarSet
    go dv (AppTy t1 t2) = foldlM go dv [t1, t2]
    go dv (TyConApp _ tys) = foldlM go dv tys
    go dv (FunTy ki arg res) = do
      dv1 <- collect_cand_qkvs (Mono ki) cur_lvl bound dvs (Mono ki)
      foldlM go dv1 [arg, res]
    go dv (TyVarTy tv)
      | is_bound tv = return dv
      | otherwise = do m_contents <- isFilledMetaTyVar_maybe tv
                       case m_contents of
                         Just ind_ty -> go dv ind_ty
                         Nothing -> go_tv dv tv
    go dv (ForAllTy (Bndr tv _) ty) = do
      dv1 <- collect_cand_qkvs (Mono $ tyVarKind tv) cur_lvl bound dv (Mono $ tyVarKind tv)
      collect_cand_qkvs_ty orig_ty cur_lvl (bound `extendVarSet` tv) dv1 ty

    go dv (TyLamTy tv ty) = do
      dv1 <- collect_cand_qkvs (Mono $ tyVarKind tv) cur_lvl bound dv (Mono $ tyVarKind tv)
      collect_cand_qkvs_ty orig_ty cur_lvl (bound `extendVarSet` tv) dv1 ty
    go dv (CastTy ty co) = do
      dv1 <- go dv ty
      collect_cand_qkvs_co co cur_lvl bound dv co
    go _ other = pprPanic "collect_cand_qkvs_ty" (ppr other)

    go_tv dv tv
      | tcTyVarLevel tv <= cur_lvl
      = return dv
      | case tcTyVarDetails tv of
          SkolemTv _ lvl -> lvl > pushTcLevel cur_lvl
          _ -> False
      = return dv
      | otherwise
      = do tv_kind <- liftZonkM $ zonkTcMonoKind (tyVarKind tv)
           collect_cand_qkvs (Mono tv_kind) cur_lvl bound dv (Mono tv_kind)

candidateQKiVarsOfKind :: TcKind -> TcM DKiVarSet
candidateQKiVarsOfKind ki = do
  cur_lvl <- getTcLevel
  collect_cand_qkvs ki cur_lvl emptyVarSet emptyDVarSet ki

collect_cand_qkvs
  :: TcKind
  -> TcLevel
  -> VarSet
  -> DKiVarSet
  -> Kind
  -> TcM DKiVarSet
collect_cand_qkvs orig_ki cur_lvl bound dvs ki = go dvs ki
  where
    is_bound kv = kv `elemVarSet` bound

    -----------------
    go :: DKiVarSet -> TcKind -> TcM DKiVarSet
    go dv (Mono ki) = go_mono dv ki
    go dv (ForAllKi kv ki) = collect_cand_qkvs orig_ki cur_lvl (bound `extendVarSet` kv) dv ki

    go_mono :: DKiVarSet -> TcMonoKind -> TcM DKiVarSet
    go_mono dv (KiConApp kc kis) = foldlM go_mono dv kis
    go_mono dv (FunKi _ k1 k2) = foldlM go_mono dv [k1, k2]
    go_mono dv (KiVarKi kv)
      | is_bound kv = return dv
      | otherwise = do
          m_contents <- isFilledMetaKiVar_maybe kv
          case m_contents of
            Just ind_ki -> go_mono dv ind_ki
            Nothing -> go_kv dv kv

    go_kv dv kv
      | tcKiVarLevel kv <= cur_lvl
      = return dv
      | case tcKiVarDetails kv of
          SkolemKv _ lvl -> lvl `strictlyDeeperThan` pushTcLevel cur_lvl
          _ -> False
      = return dv
      | kv `elemDVarSet` dv
      = return dv
      | otherwise
      = return $ dv `extendDVarSet` kv

collect_cand_qkvs_co
  :: KindCoercion
  -> TcLevel
  -> VarSet
  -> DKiVarSet
  -> KindCoercion
  -> TcM DKiVarSet
collect_cand_qkvs_co orig_co cur_lvl bound = go_co
  where
    go_co dv (Refl ki) = collect_cand_qkvs (Mono ki) cur_lvl bound dv (Mono ki)
    go_co dv (KiConAppCo _ cos) = foldM go_co dv cos
    go_co dv (FunCo _ _ co1 co2) = foldM go_co dv [co1, co2]

    go_co dv (SymCo co) = go_co dv co
    go_co dv (TransCo co1 co2) = foldM go_co dv [co1, co2]

    go_co dv (HoleCo hole) = do
      m_co <- unpackKiCoercionHole_maybe hole
      case m_co of
        Just co -> go_co dv co
        Nothing -> go_cv dv (coHoleCoVar hole)

    go_cv :: DKiVarSet -> KiCoVar -> TcM DKiVarSet
    go_cv dv cv
      | is_bound cv = return dv
      | otherwise = do
          traceTc "COLLECTING KICOVAR" (ppr cv)
          collect_cand_qkvs (Mono $ varKind cv) cur_lvl bound dv (Mono $ varKind cv)

    is_bound v = v `elemVarSet` bound

{- *********************************************************************
*                                                                      *
             Quantification
*                                                                      *
********************************************************************* -}

quantifyKiVars :: SkolemInfo -> DKiVarSet -> TcM [TcKiVar]
quantifyKiVars skol_info kvs
  | isEmptyDVarSet kvs
  = do traceTc "quantifyKiVars has nothing to quantify" empty
       return []
  | otherwise
  = do traceTc "quantifyKiVars {"
         $ vcat [ text "kvs =" <+> ppr kvs ]

       final_qkvs <- liftZonkM $ mapMaybeM zonk_quant (dVarSetElems kvs)

       traceTc "quantifyKiVars }"
         $ vcat [ text "final_qkvs =" <+> (sep $ map ppr final_qkvs) ]

       return final_qkvs
  where
    zonk_quant kv
      | not (isKiVar kv) = return Nothing
      | otherwise = Just <$> skolemizeQuantifiedKiVar skol_info kv

zonkAndSkolemize :: SkolemInfo -> TcVar -> ZonkM TcTyVar
zonkAndSkolemize skol_info var
  | isTyVarTyVar var
  = do zonked_tyvar <- zonkTcTyVarToTcTyVar var
       skolemizeQuantifiedTyVar skol_info zonked_tyvar
  | isKiVarKiVar var
  = do zonked_kivar <- zonkTcKiVarToTcKiVar var
       skolemizeQuantifiedKiVar skol_info zonked_kivar
  | otherwise
  = assertPpr (isImmutableTyVar var) (pprTyVar var)
    $ zonkTyVarKind var

skolemizeQuantifiedTyVar :: SkolemInfo -> TcTyVar -> ZonkM TcTyVar
skolemizeQuantifiedTyVar skol_info tv
  = case tcTyVarDetails tv of
      MetaTv {} -> skolemizeUnboundMetaTyVar skol_info tv
      SkolemTv _ lvl -> do kind <- zonkTcMonoKind (tyVarKind tv)
                           let details = SkolemTv skol_info lvl
                               name = tyVarName tv
                           return $ mkTcTyVar name kind details

skolemizeQuantifiedKiVar :: SkolemInfo -> TcKiVar -> ZonkM TcKiVar
skolemizeQuantifiedKiVar skol_info kv
  = case tcKiVarDetails kv of
      MetaKv {} -> skolemizeUnboundMetaKiVar skol_info kv
      SkolemKv _ lvl -> do let details = SkolemKv skol_info lvl
                               name = kiVarName kv
                           return $ mkTcKiVar name details

defaultKiVar :: TcKiVar -> TcM Bool
defaultKiVar kv
  | not (isMetaKiVar kv)
    || isKiVarKiVar kv
  = return False
  | isConcreteKiVar kv
  = do lvl <- getTcLevel
       _ <- promoteMetaKiVarTo lvl kv
       return True
  | otherwise
  = do traceTc "Defaulting a kind var to ANYKind" (ppr kv)
       panic "defaultKiVar"
       -- liftZonkM $ writeMetaKiVar kv (KiCon ANYKind)
       -- return True

defaultKiVars :: DKiVarSet -> TcM [TcKiVar]
defaultKiVars dvs = do
  let kvs = dVarSetElems dvs
  defaulted_kvs <- mapM defaultKiVar kvs
  return [ kv | (kv, False) <- kvs `zip` defaulted_kvs ]

skolemizeUnboundMetaTyVar :: SkolemInfo -> TcTyVar -> ZonkM TypeVar
skolemizeUnboundMetaTyVar skol_info tv = assertPpr (isMetaTyVar tv) (ppr tv) $ do
  check_empty tv
  ZonkGblEnv { zge_src_span = here, zge_tc_level = tc_lvl } <- getZonkGblEnv
  kind <- zonkTcMonoKind (tyVarKind tv)
  let tv_name = tyVarName tv
      final_name | isSystemName tv_name
                 = mkInternalName (nameUnique tv_name) (nameOccName tv_name) here
                 | otherwise
                 = tv_name
      details = SkolemTv skol_info (pushTcLevel tc_lvl)
      final_tv = mkTcTyVar final_name kind details

  traceZonk "Skolemizing" (ppr tv <+> text ":=" <+> ppr final_tv)
  writeMetaTyVar tv (mkTyVarTy final_tv)
  return final_tv
  where
    check_empty tv = when debugIsOn $ do
      cts <- readMetaTyVar tv
      case cts of
        Flexi -> return ()
        Indirect ty -> warnPprTrace True "skolemizeUnboundMetaTyVar" (ppr tv $$ ppr ty)
                       $ return ()
                   
skolemizeUnboundMetaKiVar :: SkolemInfo -> TcKiVar -> ZonkM KindVar
skolemizeUnboundMetaKiVar skol_info kv = assertPpr (isMetaKiVar kv) (ppr kv) $ do
  check_empty kv
  ZonkGblEnv { zge_src_span = here, zge_tc_level = tc_lvl } <- getZonkGblEnv
  let kv_name = kiVarName kv
      final_name | isSystemName kv_name
                 = mkInternalName (nameUnique kv_name) (nameOccName kv_name) here
                 | otherwise
                 = kv_name
      details = SkolemKv skol_info (pushTcLevel tc_lvl)
      final_kv = mkTcKiVar final_name details

  traceZonk "Skolemizing" (ppr kv <+> text ":=" <+> ppr final_kv)
  writeMetaKiVar kv (mkKiVarMKi final_kv)
  return final_kv
  where
    check_empty kv = when debugIsOn $ do
      cts <- readMetaKiVar kv
      case cts of
        Flexi -> return ()
        Indirect ki -> warnPprTrace True "skolemizeUnboundMetaKiVar" (ppr kv $$ ppr ki)
                       $ return ()

doNotQuantifyKiVars :: DKiVarSet -> TcM ()
doNotQuantifyKiVars dvs
  | isEmptyDVarSet dvs
  = traceTc "doNotQuantifyKiVars has nothing" empty
  | otherwise
  = do traceTc "doNotQuantifyKiVars" (ppr dvs)
       undefaulted <- defaultKiVars dvs
       let leftover_metas = filter isMetaKiVar undefaulted
       massertPpr (null leftover_metas)
         $ vcat [ text "doNotQuantifyKiVars has leftover_metas"
                , ppr leftover_metas ]
       traceTc "doNotQuantifyKiVars success" empty

{- *********************************************************************
*                                                                      *
              Promotion
*                                                                      *
********************************************************************* -}

promoteMetaKiVarTo :: HasDebugCallStack => TcLevel -> TcKiVar -> TcM Bool
promoteMetaKiVarTo tclvl kv
  | assertPpr (isMetaKiVar kv) (ppr kv)
    $ tcKiVarLevel kv `strictlyDeeperThan` tclvl
  = do cloned_kv <- cloneMetaKiVar kv
       let rhs_kv = setMetaKiVarTcLevel cloned_kv tclvl
       liftZonkM $ writeMetaKiVar kv (mkKiVarMKi rhs_kv)
       traceTc "promoteKiVar" (ppr kv <+> text "-->" <+> ppr rhs_kv)
       return True
  | otherwise
  = return False

promoteKiVarSet :: HasDebugCallStack => KiVarSet -> TcM Bool
promoteKiVarSet kvs = do
  tclvl <- getTcLevel
  bools <- mapM (promoteMetaKiVarTo tclvl)
           $ filter isPromotableMetaKiVar
           $ nonDetEltsUniqSet kvs
  return $ or bools
