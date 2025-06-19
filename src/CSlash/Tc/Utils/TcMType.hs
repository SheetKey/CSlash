module CSlash.Tc.Utils.TcMType where

import CSlash.Cs
import CSlash.Platform

import CSlash.Driver.DynFlags

-- import {-# SOURCE #-} GHC.Tc.Utils.Unify( unifyInvisibleType, tcSubMult )
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
import CSlash.Core.Type
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

newKiEvVars :: [TcPredKind] -> TcM [TcKiEvVar TcKiVar]
newKiEvVars theta = mapM newKiEvVar theta

newKiEvVar :: TcPredKind -> TcRnIf gbl lcl (TcKiEvVar TcKiVar)
newKiEvVar ki = do
  name <- newSysName (predKindOccName ki)
  return $ panic "mkLocalVarOrKiCoVar name ki"

predKindOccName :: TcPredKind -> OccName
predKindOccName ki = case classifyPredKind ki of
  EqPred {} -> mkVarOccFS (fsLit "co")
  IrredPred {} -> mkVarOccFS (fsLit "irred")
  RelPred {} -> mkVarOccFS (fsLit "relco")

newWantedWithLoc :: CtLoc -> TcPredKind -> TcM CtEvidence
newWantedWithLoc loc predki = do
  dst <- case classifyPredKind predki of
           EqPred {} -> HoleDest <$> panic "newKiCoercionHole predki"
           _ -> EvVarDest <$> panic "newKiEvVar predki"
  return $ CtWanted { ctev_dest = dst
                    , ctev_pred = panic "predki"
                    , ctev_loc = loc
                    , ctev_rewriters = emptyRewriterSet }

newWanted :: CtOrigin -> Maybe TypeOrKind -> TcPredKind -> TcM CtEvidence
newWanted orig t_or_k predki = do
  loc <- getCtLocM orig t_or_k
  newWantedWithLoc loc predki

----------------------------------------------
-- Emitting constraints
----------------------------------------------

emitWanted :: CtOrigin -> TcPredKind -> TcM AnyKiEvType 
emitWanted origin pred = do
  ev <- newWanted origin Nothing pred
  emitSimple $ mkNonCanonical ev
  return $ ctEvType ev

{- *********************************************************************
*                                                                      *
        Coercion holes
*                                                                      *
********************************************************************* -}

newKiCoercionHole :: TcPredKind -> TcM (KindCoercionHole (TcTyVar TcKiVar) TcKiVar)
newKiCoercionHole pred_ki = do
  co_var <- newKiEvVar pred_ki
  traceTc "New coercion hole:" (ppr co_var <+> colon <+> ppr pred_ki)
  ref <- newMutVar Nothing
  return $ CoercionHole { ch_co_var = co_var, ch_ref = ref }

fillKiCoercionHole :: (KindCoercionHole (TcTyVar TcKiVar) TcKiVar) -> (KindCoercion (TcTyVar TcKiVar) TcKiVar) -> TcM ()
fillKiCoercionHole (CoercionHole { ch_ref = ref, ch_co_var = cv }) co = do
  when debugIsOn $ do
    cts <- panic "readTcRef ref"
    whenIsJust cts $ \old_co ->
      panic "pprPanic Filling a filled coercion hole (ppr cv $$ ppr co $$ ppr old_co)"
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

isFilledMetaTyVar_maybe :: TcTyVar TcKiVar -> TcM (Maybe AnyType)
isFilledMetaTyVar_maybe tv
  -- | isTcTyVar tv
  | MetaVar { mv_ref = ref } <- tcVarDetails tv
  = do cts <- panic "readTcRef ref"
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
cloneMetaKiVarWithInfo info tc_lvl kv = {-assert (isTcKiVar kv) $ -}do
  ref <- newMutVar Flexi
  name' <- cloneMetaKiVarName (varName kv)
  let details = MetaVar { mv_info = info
                        , mv_ref = ref
                        , mv_tclvl = tc_lvl }
      kivar = mkTcKiVar name' details
  traceTc "cloneMetaKiVarWithInfo" (ppr kivar)
  return kivar

readMetaTyVar :: MonadIO m => TcTyVar TcKiVar -> m (MetaDetails AnyType)
readMetaTyVar tyvar = assertPpr (isMetaVar tyvar) (ppr tyvar)
  $ liftIO $ readIORef (panic "metaVarRef tyvar")
{-# SPECIALIZE readMetaTyVar :: TcTyVar TcKiVar -> TcM (MetaDetails AnyType) #-}
{-# SPECIALIZE readMetaTyVar :: TcTyVar TcKiVar -> ZonkM (MetaDetails AnyType) #-}

readMetaKiVar :: MonadIO m => TcKiVar -> m (MetaDetails AnyMonoKind)
readMetaKiVar kivar = assertPpr (isMetaVar kivar) (ppr kivar)
  $ liftIO $ readIORef (metaVarRef kivar)
{-# SPECIALIZE readMetaKiVar :: TcKiVar -> TcM (MetaDetails AnyMonoKind) #-}
{-# SPECIALIZE readMetaKiVar :: TcKiVar -> ZonkM (MetaDetails AnyMonoKind) #-}

isFilledMetaKiVar_maybe :: TcKiVar -> TcM (Maybe AnyMonoKind)
isFilledMetaKiVar_maybe kv
  | panic "isTcKiVar kv"
  , MetaVar { mv_ref = ref } <- tcVarDetails kv
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

cloneAnonMetaKiVar :: MetaInfo -> TcKiVar -> TcM TcKiVar
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

newMetaKiVarX :: KvSubst TcKiVar -> TcKiVar -> TcM (KvSubst TcKiVar, TcKiVar)
newMetaKiVarX = new_meta_kv_x TauVar

new_meta_kv_x :: MetaInfo -> KvSubst TcKiVar -> TcKiVar -> TcM (KvSubst TcKiVar, TcKiVar)
new_meta_kv_x info subst kv = do
  new_kv <- cloneAnonMetaKiVar info kv
  let subst1 = extendKvSubstWithClone subst kv new_kv
  return (subst1, new_kv)

{- *********************************************************************
*                                                                      *
             Finding variables to quantify over
*                                                                      *
********************************************************************* -}

candidateQKiVarsOfType :: TcType -> TcM DKiVarSet
candidateQKiVarsOfType ty = do
  cur_lvl <- getTcLevel
  panic "collect_cand_qkvs_ty ty cur_lvl emptyVarSet emptyDVarSet ty"

-- collect_cand_qkvs_ty :: TcType -> TcLevel -> AnyKiVarSet -> DKiVarSet -> AnyType -> TcM DKiVarSet
-- collect_cand_qkvs_ty orig_ty cur_lvl bound dvs ty = go dvs ty
--   where
--     is_bound kv = kv `elemVarSet` bound

--     go :: DKiVarSet -> TcType -> TcM DKiVarSet
--     go dv (AppTy t1 t2) = foldlM go dv [t1, t2]
--     go dv (TyConApp _ tys) = foldlM go dv tys
--     go dv (FunTy ki arg res) = do
--       dv1 <- collect_cand_qkvs (Mono ki) cur_lvl bound dvs (Mono ki)
--       foldlM go dv1 [arg, res]
--     go dv (TyVarTy tv)
--       | is_bound tv = return dv
--       | otherwise = do m_contents <- isFilledMetaTyVar_maybe tv
--                        case m_contents of
--                          Just ind_ty -> go dv ind_ty
--                          Nothing -> go_tv dv tv
--     go dv (ForAllTy (Bndr tv _) ty) = do
--       dv1 <- collect_cand_qkvs (Mono $ varKind tv) cur_lvl bound dv (Mono $ varKind tv)
--       collect_cand_qkvs_ty orig_ty cur_lvl (bound `extendVarSet` tv) dv1 ty

--     go dv (TyLamTy tv ty) = do
--       dv1 <- collect_cand_qkvs (Mono $ varKind tv) cur_lvl bound dv (Mono $ varKind tv)
--       collect_cand_qkvs_ty orig_ty cur_lvl (bound `extendVarSet` tv) dv1 ty

--     go dv (BigTyLamTy kv ty) = 
--       collect_cand_qkvs_ty orig_ty cur_lvl (bound `extendVarSet` kv) dv ty

--     go dv (CastTy ty co) = do
--       dv1 <- go dv ty
--       collect_cand_qkvs_co co cur_lvl bound dv co

--     go dv (Embed ki) = collect_cand_qkvs (Mono ki) cur_lvl bound dv (Mono ki)

--     go _ other = pprPanic "collect_cand_qkvs_ty" (ppr other)

--     go_tv dv tv
--       | varLevel tv <= cur_lvl
--       = return dv
--       | case tcVarDetails tv of
--           SkolemVar _ lvl -> lvl > pushTcLevel cur_lvl
--           _ -> False
--       = return dv
--       | otherwise
--       = do tv_kind <- liftZonkM $ zonkTcMonoKind (varKind tv)
--            collect_cand_qkvs (Mono tv_kind) cur_lvl bound dv (Mono tv_kind)

candidateQKiVarsOfKind :: TcKind -> TcM DKiVarSet
candidateQKiVarsOfKind ki = do
  cur_lvl <- getTcLevel
  panic "collect_cand_qkvs ki cur_lvl emptyVarSet emptyDVarSet ki"

-- collect_cand_qkvs
--   :: TcKind
--   -> TcLevel
--   -> AnyKiVarSet
--   -> DKiVarSet
--   -> AnyKind
--   -> TcM DKiVarSet
-- collect_cand_qkvs orig_ki cur_lvl bound dvs ki = go dvs ki
--   where
--     is_bound kv = kv `elemVarSet` bound

--     -----------------
--     go :: DKiVarSet -> TcKind -> TcM DKiVarSet
--     go dv (Mono ki) = go_mono dv ki
--     go dv (ForAllKi kv ki) = collect_cand_qkvs orig_ki cur_lvl (bound `extendVarSet` kv) dv ki

--     go_mono :: DKiVarSet -> TcMonoKind -> TcM DKiVarSet
--     go_mono dv (KiConApp kc kis) = foldlM go_mono dv kis
--     go_mono dv (FunKi _ k1 k2) = foldlM go_mono dv [k1, k2]
--     go_mono dv (KiVarKi kv)
--       | is_bound kv = return dv
--       | otherwise = do
--           m_contents <- isFilledMetaKiVar_maybe kv
--           case m_contents of
--             Just ind_ki -> go_mono dv ind_ki
--             Nothing -> go_kv dv kv

--     go_kv dv kv
--       | varLevel kv <= cur_lvl
--       = return dv
--       | case tcVarDetails kv of
--           SkolemVar _ lvl -> lvl > pushTcLevel cur_lvl
--           _ -> False
--       = return dv
--       | kv `elemDVarSet` dv
--       = return dv
--       | otherwise
--       = return $ dv `extendDVarSet` kv

-- collect_cand_qkvs_co
--   :: KindCoercion (TcTyVar TcKiVar) TcKiVar
--   -> TcLevel
--   -> AnyKiVarSet
--   -> DKiVarSet
--   -> KindCoercion (TcTyVar TcKiVar) TcKiVar
--   -> TcM DKiVarSet
-- collect_cand_qkvs_co orig_co cur_lvl bound = go_co
--   where
--     go_co dv (Refl ki) = collect_cand_qkvs (Mono ki) cur_lvl bound dv (Mono ki)
--     go_co dv (KiConAppCo _ cos) = foldM go_co dv cos
--     go_co dv (FunCo _ _ co1 co2) = foldM go_co dv [co1, co2]

--     go_co dv (SymCo co) = go_co dv co
--     go_co dv (TransCo co1 co2) = foldM go_co dv [co1, co2]

--     go_co dv (HoleCo hole) = do
--       m_co <- unpackKiCoercionHole_maybe hole
--       case m_co of
--         Just co -> go_co dv co
--         Nothing -> go_cv dv (coHoleCoVar hole)

--     go_co dv (KiCoVarCo cv) = go_cv dv cv

--     go_cv :: DKiVarSet -> KiCoVar KiVar -> TcM DKiVarSet
--     go_cv dv cv
--       | is_bound cv = return dv
--       | otherwise = do
--           traceTc "COLLECTING KICOVAR" (ppr cv)
--           collect_cand_qkvs (Mono $ varKind cv) cur_lvl bound dv (Mono $ varKind cv)

--     is_bound v = v `elemVarSet` bound

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

       final_qkvs <- liftZonkM $ mapMaybeM zonk_quant (panic "dVarSetElems kvs")

       traceTc "quantifyKiVars }"
         $ vcat [ text "final_qkvs =" <+> (sep $ map ppr final_qkvs) ]

       return final_qkvs
  where
    zonk_quant kv
      | not (panic "isKiVar kv") = return Nothing
      | otherwise = Just <$> skolemizeQuantifiedKiVar skol_info kv

zonkAndSkolemize :: SkolemInfo -> TcTyVar TcKiVar -> ZonkM (TcTyVar TcKiVar)
zonkAndSkolemize skol_info var
  | isTcVarVar var
  = do zonked_tyvar <- zonkTcTyVarToTcTyVar var
       skolemizeQuantifiedTyVar skol_info zonked_tyvar
  -- | isTcVarVar var
  -- = do zonked_kivar <- zonkTcKiVarToTcKiVar var
  --      skolemizeQuantifiedKiVar skol_info zonked_kivar
  | otherwise
  = assertPpr (isImmutableVar var) (panic "pprTyVar var")
    $ panic "zonkTyVarKind var"

skolemizeQuantifiedTyVar :: SkolemInfo -> (TcTyVar TcKiVar) -> ZonkM (TcTyVar TcKiVar)
skolemizeQuantifiedTyVar skol_info tv
  = case tcVarDetails tv of
      MetaVar {} -> panic "skolemizeUnboundMetaTyVar skol_info tv"
      SkolemVar _ lvl -> do kind <- zonkTcMonoKind (panic "varKind tv")
                            let details = SkolemVar skol_info lvl
                                name = varName tv
                            return $ mkTcTyVar name kind details

skolemizeQuantifiedKiVar :: SkolemInfo -> TcKiVar -> ZonkM TcKiVar
skolemizeQuantifiedKiVar skol_info kv
  = case tcVarDetails kv of
      MetaVar {} -> panic "skolemizeUnboundMetaKiVar skol_info kv"
      SkolemVar _ lvl -> do let details = SkolemVar skol_info lvl
                                name = varName kv
                            return $ mkTcKiVar name details

defaultKiVar :: TcKiVar -> TcM Bool
defaultKiVar kv
  | not (panic "isMetaKiVar kv")
    || isTcVarVar kv
  = return False
  | isConcreteVar kv
  = do lvl <- getTcLevel
       _ <- promoteMetaKiVarTo lvl kv
       return True
  | otherwise
  = return False

defaultKiVars :: DKiVarSet -> TcM [TcKiVar]
defaultKiVars dvs = do
  let kvs = dVarSetElems dvs
  defaulted_kvs <- panic "mapM defaultKiVar kvs"
  panic "return [ kv | (kv, False) <- kvs `zip` defaulted_kvs ]"

skolemizeUnboundMetaTyVar :: SkolemInfo -> TcTyVar TcKiVar -> ZonkM (TyVar KiVar)
skolemizeUnboundMetaTyVar skol_info tv = assertPpr (isMetaVar tv) (ppr tv) $ do
  check_empty tv
  ZonkGblEnv { zge_src_span = here, zge_tc_level = tc_lvl } <- getZonkGblEnv
  kind <- zonkTcMonoKind (panic "varKind tv")
  let tv_name = varName tv
      final_name | isSystemName tv_name
                 = mkInternalName (nameUnique tv_name) (nameOccName tv_name) here
                 | otherwise
                 = tv_name
      details = SkolemVar skol_info (pushTcLevel tc_lvl)
      final_tv = mkTcTyVar final_name kind details

  traceZonk "Skolemizing" (ppr tv <+> text ":=" <+> ppr final_tv)
  writeMetaTyVar tv (mkTyVarTy final_tv)
  panic "return final_tv"
  where
    check_empty tv = when debugIsOn $ do
      cts <- readMetaTyVar tv
      case cts of
        Flexi -> return ()
        Indirect ty -> warnPprTrace True "skolemizeUnboundMetaTyVar" (ppr tv $$ ppr ty)
                       $ return ()
                   
skolemizeUnboundMetaKiVar :: SkolemInfo -> TcKiVar -> ZonkM KiVar
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
  writeMetaKiVar kv (mkKiVarKi final_kv)
  panic "return final_kv"
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
       let leftover_metas = filter isMetaVar undefaulted
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
  | assertPpr (isMetaVar kv) (ppr kv)
    $ varLevel kv `strictlyDeeperThan` tclvl
  = do cloned_kv <- cloneMetaKiVar kv
       let rhs_kv = setMetaVarTcLevel cloned_kv tclvl
       liftZonkM $ writeMetaKiVar kv (mkKiVarKi rhs_kv)
       traceTc "promoteKiVar" (ppr kv <+> text "-->" <+> ppr rhs_kv)
       return True
  | otherwise
  = return False

promoteKiVarSet :: HasDebugCallStack => KiVarSet -> TcM Bool
promoteKiVarSet kvs = do
  tclvl <- getTcLevel
  bools <- mapM (promoteMetaKiVarTo tclvl)
           $ filter isPromotableMetaVar
           $ panic "nonDetEltsUniqSet kvs"
  return $ or bools
