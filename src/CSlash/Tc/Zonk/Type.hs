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

import CSlash.Types.Name
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
zonkTyBndrX :: TcTyVar -> ZonkBndrTcM TypeVar
zonkTyBndrX tv = assertPpr (isImmutableTyVar tv) (ppr tv) $ do
  ki <- noBinders $ zonkTcMonoKindToMonoKindX (tyVarKind tv)
  let tv' = mkTyVar (tyVarName tv) ki
  extendTyZonkEnv tv'
  return tv'

{-# INLINE zonkKiBndrX #-}
zonkKiBndrX :: TcKiVar -> ZonkBndrTcM KindVar
zonkKiBndrX kv = assertPpr (isImmutableKiVar kv) (ppr kv) $ do
  let kv' = mkKiVar (kiVarName kv)
  extendKiZonkEnv kv'
  return kv'

{-# INLINE zonkKiVarBindersX #-}
zonkKiVarBindersX :: [TcKiVar] -> ZonkBndrTcM [KindVar]
zonkKiVarBindersX = traverse zonkKiVarBinderX

{-# INLINE zonkKiVarBinderX #-}
zonkKiVarBinderX :: TcKiVar -> ZonkBndrTcM KindVar
zonkKiVarBinderX kv = zonkKiBndrX kv

zonkTyVarOcc :: HasDebugCallStack => TcTyVar -> ZonkTcM Type
zonkTyVarOcc tv = do
  ZonkEnv { ze_tv_env = tv_env } <- getZonkEnv
  let lookup_in_tv_env = case lookupVarEnv tv_env tv of
                           Nothing -> mkTyVarTy <$> updateTyVarKindM zonkTcMonoKindToMonoKindX tv
                           Just tv' -> return $ mkTyVarTy tv'

      finish_meta ty = do
        extendMetaTvEnv tv ty
        return ty

      zonk_meta ref Flexi = do
        kind <- zonkTcMonoKindToMonoKindX (tyVarKind tv)
        ty <- commitFlexiTv tv kind
        lift $ liftZonkM $ writeMetaTyVarRef tv ref ty
        finish_meta ty

      zonk_meta _ (Indirect ty) = do
        zty <- zonkTcTypeToTypeX ty
        finish_meta zty

  if isTcTyVar tv
    then case tcTyVarDetails tv of
           SkolemTv {} -> lookup_in_tv_env
           MetaTv { mtv_ref = ref } -> do
             mb_ty <- lookupMetaTv tv
             case mb_ty of
               Just ty -> return ty
               Nothing -> do mtv_details <- readTcRef ref
                             zonk_meta ref mtv_details
    else lookup_in_tv_env

extendMetaTvEnv :: TcTyVar -> Type -> ZonkTcM ()
extendMetaTvEnv tv ty = ZonkT $ \ (ZonkEnv { ze_meta_tv_env = mtv_env_ref }) ->
  updTcRef mtv_env_ref (\env -> extendVarEnv env tv ty)

lookupMetaTv :: TcTyVar -> ZonkTcM (Maybe Type)
lookupMetaTv tv = ZonkT $ \ (ZonkEnv { ze_meta_tv_env = mtv_env_ref }) -> do
  mtv_env <- readTcRef mtv_env_ref
  return $ lookupVarEnv mtv_env tv

commitFlexiTv :: TcTyVar -> MonoKind -> ZonkTcM Type
commitFlexiTv tv zonked_kind = do
  flexi <- ze_flexi <$> getZonkEnv
  lift $ case flexi of
    NoFlexi -> pprPanic "NoFlexi" (ppr tv <+> colon <+> ppr zonked_kind) 

zonk_typemapper :: TypeMapper ZonkEnv TcM
zonk_typemapper = TypeMapper
  { tcm_tyvar = \env tv -> runZonkT (zonkTyVarOcc tv) env
  , tcm_tybinder = \env tv _ k -> flip runZonkT env $ runZonkBndrT (zonkTyBndrX tv)
                                  $ \tv' -> ZonkT $ \env' -> (k env' tv')
  , tcm_tylambinder = \env tv k -> flip runZonkT env $ runZonkBndrT (zonkTyBndrX tv)
                                   $ \tv' -> ZonkT $ \env' -> (k env' tv')
  , tcm_tylamkibinder = \env kv k -> flip runZonkT env $ runZonkBndrT (zonkKiBndrX kv)
                                     $ \kv' -> ZonkT $ \env' -> (k env' kv')
  , tcm_tycon = \tc -> zonkTcTyConToTyCon tc
  , tcm_embed_mono_ki = \env ki -> runZonkT (zonkTcMonoKindToMonoKindX ki) env
  }

zonkTcTyConToTyCon :: TcTyCon -> TcM TyCon
zonkTcTyConToTyCon tc
  | isTcTyCon tc = do
      thing <- tcLookupGlobalOnly (getName tc)
      case thing of
        ATyCon real_tc -> return real_tc
        _ -> pprPanic "zonkTcTyCon" (ppr tc $$ ppr thing)
  | otherwise = return tc

zonkTcTypeToTypeX :: TcType -> ZonkTcM Type
zonkTcTypesToTypesX :: [TcType] -> ZonkTcM [Type]
(zonkTcTypeToTypeX, zonkTcTypesToTypesX) = case mapTypeX zonk_typemapper of
  (zty, ztys) -> (ZonkT . flip zty, ZonkT . flip ztys)

zonkKiVarOcc :: HasDebugCallStack => TcKiVar -> ZonkTcM MonoKind
zonkKiVarOcc kv = do
  ZonkEnv { ze_kv_env = kv_env } <- getZonkEnv
  let lookup_in_kv_env = case lookupVarEnv kv_env kv of
                           Nothing -> return $ mkKiVarMKi kv
                           Just kv' -> return $ mkKiVarMKi kv'

      finish_meta ki = do
        extendMetaKvEnv kv ki
        return ki

      zonk_meta ref Flexi = do
        ki <- commitFlexiKv kv
        lift $ liftZonkM $ writeMetaKiVarRef kv ref ki
        finish_meta ki

      zonk_meta _ (Indirect ki) = do
        zki <- zonkTcMonoKindToMonoKindX ki
        finish_meta zki

  if isTcKiVar kv
    then case tcKiVarDetails kv of
           SkolemKv {} -> lookup_in_kv_env
           MetaKv { mkv_ref = ref } -> do
             mb_ki <- lookupMetaKv kv
             case mb_ki of
               Just ki -> return ki
               Nothing -> do mkv_details <- readTcRef ref
                             zonk_meta ref mkv_details
    else lookup_in_kv_env

extendMetaKvEnv :: TcKiVar -> MonoKind -> ZonkTcM ()
extendMetaKvEnv kv ki = ZonkT $ \ (ZonkEnv { ze_meta_kv_env = mkv_env_ref }) ->
  updTcRef mkv_env_ref (\env -> extendVarEnv env kv ki)

lookupMetaKv :: TcKiVar -> ZonkTcM (Maybe MonoKind)
lookupMetaKv kv = ZonkT $ \ (ZonkEnv { ze_meta_kv_env = mkv_env_ref }) -> do
  mkv_env <- readTcRef mkv_env_ref
  return $ lookupVarEnv mkv_env kv

commitFlexiKv :: TcKiVar -> ZonkTcM MonoKind
commitFlexiKv kv = do
  flexi <- ze_flexi <$> getZonkEnv
  lift $ case flexi of
    NoFlexi -> pprPanic "NoFlexi" (ppr kv)

zonk_kindmapper :: KindMapper ZonkEnv TcM
zonk_kindmapper = KindMapper
  { km_kivar = \env kv -> runZonkT (zonkKiVarOcc kv) env
  , km_kibinder = \env kv k -> flip runZonkT env $ runZonkBndrT (zonkKiBndrX kv)
                               $ \kv' -> ZonkT $ \env' -> (k env' kv')
  }

zonkTcKindToKindX :: TcKind -> ZonkTcM Kind
zonkTcKindsToKindsX :: [TcKind] -> ZonkTcM [Kind]
(zonkTcKindToKindX, zonkTcKindsToKindsX) = case mapKindX zonk_kindmapper of
  (zki, zkis) -> (ZonkT . flip zki, ZonkT . flip zkis)

zonkTcMonoKindToMonoKindX :: TcMonoKind -> ZonkTcM MonoKind
zonkTcMonoKindToMonoKindX ki = do
  ki' <- zonkTcKindToKindX $ Mono ki
  case ki' of
    Mono mki -> return mki
    _ -> pprPanic "zonkTcMonoKindToMonoKindX" (ppr ki $$ ppr ki')
