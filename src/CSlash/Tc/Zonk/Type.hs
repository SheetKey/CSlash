module CSlash.Tc.Zonk.Type
  ( module CSlash.Tc.Zonk.Type
  , module CSlash.Tc.Zonk.Env
  ) where

import Prelude hiding ((<>))

import CSlash.Builtin.Types

import CSlash.Core.Type.Ppr ( pprTyVar )

import CSlash.Cs

-- import {-# SOURCE #-} GHC.Tc.Gen.Splice (runTopSplice)
import CSlash.Tc.Types ( TcM )
import CSlash.Tc.Types.TcRef
-- import GHC.Tc.TyCl.Build ( TcMethInfo, MethInfo )
import CSlash.Tc.Utils.Env ( tcLookupGlobalOnly )
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Utils.Monad ( setSrcSpanA, liftZonkM, traceTc, addErr )
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Errors.Types
import CSlash.Tc.Zonk.Env
import CSlash.Tc.Zonk.TcType
       ( tcInitTidyEnv{-, tcInitOpenTidyEnv -}
       , writeMetaTyVarRef
       , writeMetaKiVarRef )

import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Core.TyCon

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Monad
import CSlash.Utils.Panic

import CSlash.Core

import CSlash.Types.Name hiding (varName)
import CSlash.Types.Name.Env
import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Id
import CSlash.Types.TypeEnv
import CSlash.Types.Basic
import CSlash.Types.SrcLoc
import CSlash.Types.Unique.Set
import CSlash.Types.Unique.FM
import CSlash.Types.TyThing

import CSlash.Tc.Types.BasicTypes

import CSlash.Data.Maybe
import CSlash.Data.Bag

import Control.Monad
import Control.Monad.Trans.Class ( lift )
import Data.Semigroup

type ZonkTcM = ZonkT TcM

type ZonkBndrTcM = ZonkBndrT TcM

{-# INLINE zonkTyBndrX #-}
zonkTyBndrX :: TcTyVar TcKiVar -> ZonkBndrTcM (TyVar KiVar)
zonkTyBndrX tv = assertPpr (isImmutableVar tv) (ppr tv) $ do
  ki <- noBinders $ zonkTcMonoKindToMonoKindX (varKind tv)
  let tv' = mkTyVar (varName tv) ki
  panic "extendTyZonkEnv tv'"
  return tv'

{-# INLINE zonkKiBndrX #-}
zonkKiBndrX :: TcKiVar -> ZonkBndrTcM KiVar
zonkKiBndrX kv = assertPpr (isImmutableVar kv) (ppr kv) $ do
  let kv' = mkKiVar (varName kv)
  panic "extendKiZonkEnv kv'"
  return kv'

{-# INLINE zonkKiVarBindersX #-}
zonkKiVarBindersX :: [TcKiVar] -> ZonkBndrTcM [KiVar]
zonkKiVarBindersX = traverse zonkKiVarBinderX

{-# INLINE zonkKiVarBinderX #-}
zonkKiVarBinderX :: TcKiVar -> ZonkBndrTcM KiVar
zonkKiVarBinderX kv = zonkKiBndrX kv

zonkTyVarOcc :: HasDebugCallStack => TcTyVar TcKiVar -> ZonkTcM (Type (TyVar KiVar) KiVar)
zonkTyVarOcc tv = do
  ZonkEnv { ze_tv_env = tv_env } <- getZonkEnv
  let lookup_in_tv_env = panic "lookup_in_tv_env"
        -- case lookupVarEnv tv_env tv of
        --                    Nothing -> mkTyVarTy <$> updateVarKindM zonkTcMonoKindToMonoKindX tv
        --                    Just tv' -> return $ mkTyVarTy tv'

      finish_meta ty = do
        extendMetaTvEnv tv ty
        return ty

      zonk_meta ref Flexi = do
        kind <- zonkTcMonoKindToMonoKindX (varKind tv)
        ty <- commitFlexiTv tv kind
        lift $ liftZonkM $ panic "writeMetaTyVarRef tv ref ty"
        finish_meta ty

      zonk_meta _ (Indirect ty) = do
        zty <- zonkTcTypeToTypeX ty
        finish_meta zty

  if True {-isTcTyVar tv-}
    then case tcVarDetails tv of
           SkolemVar {} -> lookup_in_tv_env
           MetaVar { mv_ref = ref } -> do
             mb_ty <- lookupMetaTv tv
             case mb_ty of
               Just ty -> return ty
               Nothing -> do mtv_details <- panic "readTcRef ref"
                             zonk_meta ref mtv_details
    else lookup_in_tv_env

extendMetaTvEnv :: TcTyVar TcKiVar -> Type (TyVar KiVar) KiVar -> ZonkTcM ()
extendMetaTvEnv tv ty = ZonkT $ \ (ZonkEnv { ze_meta_tv_env = mtv_env_ref }) ->
  updTcRef mtv_env_ref (\env -> panic "extendVarEnv env tv ty")

lookupMetaTv :: TcTyVar TcKiVar -> ZonkTcM (Maybe (Type (TyVar KiVar) KiVar))
lookupMetaTv tv = ZonkT $ \ (ZonkEnv { ze_meta_tv_env = mtv_env_ref }) -> do
  mtv_env <- readTcRef mtv_env_ref
  return $ panic "lookupVarEnv mtv_env tv"

commitFlexiTv :: TcTyVar TcKiVar -> MonoKind KiVar -> ZonkTcM (Type (TyVar KiVar) KiVar)
commitFlexiTv tv zonked_kind = do
  flexi <- ze_flexi <$> getZonkEnv
  lift $ case flexi of
    NoFlexi -> pprPanic "NoFlexi" (ppr tv <+> colon <+> ppr zonked_kind) 

zonk_typemapper :: TypeMapper (TcTyVar TcKiVar) TcKiVar (TyVar KiVar) KiVar ZonkEnv TcM
zonk_typemapper = panic "zonk_typemapper"
  -- TypeMapper
  -- { tcm_tyvar = \env tv -> runZonkT (zonkTyVarOcc tv) env
  -- , tcm_tybinder = \env tv _ k -> flip runZonkT env $ runZonkBndrT (zonkTyBndrX tv)
  --                                 $ \tv' -> ZonkT $ \env' -> (k env' tv')
  -- , tcm_tylambinder = \env tv k -> flip runZonkT env $ runZonkBndrT (zonkTyBndrX tv)
  --                                  $ \tv' -> ZonkT $ \env' -> (k env' tv')
  -- , tcm_tylamkibinder = \env kv k -> flip runZonkT env $ runZonkBndrT (zonkKiBndrX kv)
  --                                    $ \kv' -> ZonkT $ \env' -> (k env' kv')
  -- , tcm_tycon = \tc -> zonkTcTyConToTyCon tc
  -- , tcm_embed_mono_ki = \env ki -> runZonkT (zonkTcMonoKindToMonoKindX ki) env
  -- }

zonkTcTyConToTyCon :: TcTyCon -> TcM (TyCon (TyVar KiVar) KiVar)
zonkTcTyConToTyCon tc
  | isTcTyCon tc = do
      thing <- tcLookupGlobalOnly (getName tc)
      case thing of
        ATyCon real_tc -> return real_tc
        _ -> pprPanic "zonkTcTyCon" (ppr tc $$ ppr thing)
  | otherwise = panic "return tc"

zonkTcTypeToTypeX :: TcType -> ZonkTcM (Type (TyVar KiVar) KiVar)
zonkTcTypesToTypesX :: [TcType] -> ZonkTcM [Type (TyVar KiVar) KiVar]
(zonkTcTypeToTypeX, zonkTcTypesToTypesX) = case mapTypeX zonk_typemapper of
  (zty, ztys) -> (ZonkT . flip zty, ZonkT . flip ztys)

zonkKiVarOcc :: HasDebugCallStack => TcKiVar -> ZonkTcM (MonoKind KiVar)
zonkKiVarOcc kv = do
  ZonkEnv { ze_kv_env = kv_env } <- getZonkEnv
  let lookup_in_kv_env = panic "lookup_in_kv_env"
        -- case lookupVarEnv kv_env kv of
        --                    Nothing -> return $ mkKiVarKi kv
        --                    Just kv' -> return $ mkKiVarKi kv'

      finish_meta ki = do
        extendMetaKvEnv kv ki
        return ki

      zonk_meta ref Flexi = do
        ki <- commitFlexiKv kv
        lift $ liftZonkM $ panic "writeMetaKiVarRef kv ref ki"
        finish_meta ki

      zonk_meta _ (Indirect ki) = do
        zki <- zonkTcMonoKindToMonoKindX ki
        finish_meta zki

  if True {-isTcKiVar kv-}
    then case tcVarDetails kv of
           SkolemVar {} -> lookup_in_kv_env
           MetaVar { mv_ref = ref } -> do
             mb_ki <- lookupMetaKv kv
             case mb_ki of
               Just ki -> return ki
               Nothing -> do mkv_details <- panic "readTcRef ref"
                             zonk_meta ref mkv_details
    else lookup_in_kv_env

extendMetaKvEnv :: TcKiVar -> MonoKind KiVar -> ZonkTcM ()
extendMetaKvEnv kv ki = ZonkT $ \ (ZonkEnv { ze_meta_kv_env = mkv_env_ref }) ->
  updTcRef mkv_env_ref (\env -> panic "extendVarEnv env kv ki")

lookupMetaKv :: TcKiVar -> ZonkTcM (Maybe (MonoKind KiVar))
lookupMetaKv kv = ZonkT $ \ (ZonkEnv { ze_meta_kv_env = mkv_env_ref }) -> do
  mkv_env <- readTcRef mkv_env_ref
  return $ panic "lookupVarEnv mkv_env kv"

commitFlexiKv :: TcKiVar -> ZonkTcM (MonoKind KiVar)
commitFlexiKv kv = do
  flexi <- ze_flexi <$> getZonkEnv
  lift $ case flexi of
    NoFlexi -> pprPanic "NoFlexi" (ppr kv)

zonk_kindmapper :: KiCoMapper (TcTyVar TcKiVar) TcKiVar (TyVar KiVar) KiVar ZonkEnv TcM
zonk_kindmapper = panic "zonk_kindmapper"
  -- KindMapper
  -- { km_kivar = \env kv -> runZonkT (zonkKiVarOcc kv) env
  -- , km_kibinder = \env kv k -> flip runZonkT env $ runZonkBndrT (zonkKiBndrX kv)
  --                              $ \kv' -> ZonkT $ \env' -> (k env' kv')
  -- }

zonkTcKindToKindX :: TcKind -> ZonkTcM (Kind KiVar)
zonkTcKindsToKindsX :: [TcKind] -> ZonkTcM [Kind KiVar]
(zonkTcKindToKindX, zonkTcKindsToKindsX) = case mapKindX zonk_kindmapper of
  (zki, zkis) -> (ZonkT . flip zki, ZonkT . flip zkis)

zonkTcMonoKindToMonoKindX :: TcMonoKind -> ZonkTcM (MonoKind KiVar)
zonkTcMonoKindToMonoKindX ki = do
  ki' <- zonkTcKindToKindX $ Mono ki
  case ki' of
    Mono mki -> return mki
    _ -> pprPanic "zonkTcMonoKindToMonoKindX" (ppr ki $$ ppr ki')

{- *********************************************************************
*                                                                      *
             Checking for coercion holes
*                                                                      *
********************************************************************* -}

unpackKiCoercionHole_maybe :: KindCoercionHole tv kv -> TcM (Maybe (KindCoercion tv kv))
unpackKiCoercionHole_maybe (CoercionHole { ch_ref = ref }) = readTcRef ref

zonkRewriterSet :: RewriterSet -> TcM RewriterSet
zonkRewriterSet (RewriterSet set) = nonDetStrictFoldUniqSet go (return emptyRewriterSet) set
  where
    --go :: KindCoercionHole -> TcM RewriterSet -> TcM RewriterSet
    go hole m_acc = unionRewriterSet <$> check_hole hole <*> m_acc

    --check_hole :: KindCoercionHole -> TcM RewriterSet
    check_hole hole = do
      m_co <- unpackKiCoercionHole_maybe hole
      case m_co of
        Nothing -> return $ unitRewriterSet hole
        Just co -> unUCHM (check_co co)

    -- check_ki :: MonoKind -> UnfilledCoercionHoleMonoid
    -- check_co :: KindCoercion -> UnfilledCoercionHoleMonoid
    (check_ki, _, check_co, _) = foldMonoKiCo folder ()

    --folder :: MKiCoFolder () UnfilledCoercionHoleMonoid
    folder = panic "folder"
      -- MKiCoFolder { kcf_kivar = \_ _ -> mempty
      --                    , kcf_covar = \_ cv -> check_ki (varKind cv)
      --                    , kcf_hole = \_ -> UCHM . check_hole }

newtype UnfilledCoercionHoleMonoid = UCHM { unUCHM :: TcM RewriterSet }

instance Semigroup UnfilledCoercionHoleMonoid where
  UCHM l <> UCHM r = UCHM (unionRewriterSet <$> l <*> r)

instance Monoid UnfilledCoercionHoleMonoid where
  mempty = UCHM (return emptyRewriterSet)
