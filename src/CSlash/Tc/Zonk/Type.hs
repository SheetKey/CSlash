{-# LANGUAGE RecordWildCards #-}

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
       , writeMetaKiVarRef
       , checkKiCoercionHole )

import CSlash.Core.Type
import CSlash.Core.Type.Rep (mkNakedTyConTy)
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

wrapLocZonkMA
  :: (a -> ZonkTcM b)
  -> GenLocated (EpAnn ann) a
  -> ZonkTcM (GenLocated (EpAnn ann) b)
wrapLocZonkMA fn (L loc a) = ZonkT $ \ze -> setSrcSpanA loc $ do
  b <- runZonkT (fn a) ze
  return (L loc b)

{-# INLINE zonkTyBndrX #-}
zonkTyBndrX :: AnyTyVar AnyKiVar -> ZonkBndrTcM (TyVar KiVar)
zonkTyBndrX tv = handleAnyTv
                 (\_ -> res)
                 (\tctv -> assertPpr (isImmutableVar tctv) (ppr tctv) res)
                 tv
  where
    res = do
      ki <- noBinders $ zonkTcMonoKindToMonoKindX (varKind tv)
      let tv' = mkTyVar (varName tv) ki
      extendTyZonkEnv tv'
      return tv'

{-# INLINE zonkKiBndrX #-}
zonkKiBndrX :: AnyKiVar -> ZonkBndrTcM KiVar
zonkKiBndrX kv = handleAnyKv
                 (\_ -> res)
                 (\tckv -> assertPpr (isImmutableVar tckv) (ppr tckv) res)
                 kv
  where
    res = do
      let kv' = mkKiVar (varName kv)
      extendKiZonkEnv kv'
      return kv'

{-# INLINE zonkKiVarBindersX #-}
zonkKiVarBindersX :: [AnyKiVar] -> ZonkBndrTcM [KiVar]
zonkKiVarBindersX = traverse zonkKiVarBinderX

{-# INLINE zonkKiVarBinderX #-}
zonkKiVarBinderX :: AnyKiVar -> ZonkBndrTcM KiVar
zonkKiVarBinderX kv = zonkKiBndrX kv

zonkTyVarOcc :: HasDebugCallStack => AnyTyVar AnyKiVar -> ZonkTcM (Type (TyVar KiVar) KiVar)
zonkTyVarOcc = handleAnyTv f_any f_tc
  where
    f_tc tv = do
      ZonkEnv { ze_tv_env = tv_env } <- getZonkEnv
      let lookup_in_tv_env :: ZonkTcM (Type (TyVar KiVar) KiVar)
          lookup_in_tv_env = case lookupVarEnv_Directly tv_env (varUnique tv) of
            Nothing -> panic "zonkTyVarOcc bad skolem"
              -- mkTyVarTy <$> updateVarKindM zonkTcMonoKindToMonoKindX tv
            Just tv' -> return $ mkTyVarTy tv'
      
          finish_meta :: Type (TyVar KiVar) KiVar -> ZonkTcM (Type (TyVar KiVar) KiVar)
          finish_meta ty = do
            extendMetaTvEnv tv ty
            return ty
      
          zonk_meta
            :: TcRef (MetaDetails (AnyType))
            -> MetaDetails (AnyType)
            -> ZonkTcM (Type (TyVar KiVar) KiVar)
            
          zonk_meta ref Flexi = do
            kind <- zonkTcMonoKindToMonoKindX (varKind tv)
            ty <- commitFlexiTv tv kind
            -- Not necessary to write, since we are adding to the ZonkEnv
            -- (also we can't write a Type to a ref of AnyType)
            -- lift $ liftZonkM $ writeMetaTyVarRef tv ref ty
            finish_meta ty
      
          zonk_meta _ (Indirect ty) = do
            zty <- zonkTcTypeToTypeX ty
            finish_meta zty

      case tcVarDetails tv of
        SkolemVar {} -> lookup_in_tv_env
        MetaVar { mv_ref = ref } -> do
          mb_ty <- lookupMetaTv tv
          case mb_ty of
            Just ty -> return ty
            Nothing -> do mtv_details <- readTcRef ref
                          zonk_meta ref mtv_details

    f_any tv = mkTyVarTy <$> changeVarKindM zonkTcMonoKindToMonoKindX tv

extendMetaTvEnv :: TcTyVar AnyKiVar -> Type (TyVar KiVar) KiVar -> ZonkTcM ()
extendMetaTvEnv tv ty = ZonkT $ \ (ZonkEnv { ze_meta_tv_env = mtv_env_ref }) ->
  updTcRef mtv_env_ref (\env -> panic "extendVarEnv env tv ty")

lookupMetaTv :: TcTyVar AnyKiVar -> ZonkTcM (Maybe (Type (TyVar KiVar) KiVar))
lookupMetaTv tv = ZonkT $ \ (ZonkEnv { ze_meta_tv_env = mtv_env_ref }) -> do
  mtv_env <- readTcRef mtv_env_ref
  return $ lookupVarEnv mtv_env tv

commitFlexiTv :: TcTyVar AnyKiVar -> MonoKind KiVar -> ZonkTcM (Type (TyVar KiVar) KiVar)
commitFlexiTv tv zonked_kind = do
  flexi <- ze_flexi <$> getZonkEnv
  lift $ case flexi of
    NoFlexi -> pprPanic "NoFlexi" (ppr tv <+> colon <+> ppr zonked_kind) 

zonk_typemapper :: TypeMapper (AnyTyVar AnyKiVar) AnyKiVar (TyVar KiVar) KiVar ZonkEnv TcM
zonk_typemapper = TypeMapper
  { tm_tyvar = \env tv -> runZonkT (zonkTyVarOcc tv) env
  , tm_tybinder = \env tv _ k -> flip runZonkT env $ runZonkBndrT (zonkTyBndrX tv)
                                 $ \tv' -> ZonkT $ \env' -> (k env' tv')
  , tm_tylambinder = \env tv k -> flip runZonkT env $ runZonkBndrT (zonkTyBndrX tv)
                                  $ \tv' -> ZonkT $ \env' -> (k env' tv')
  , tm_tylamkibinder = \env kv k -> flip runZonkT env $ runZonkBndrT (zonkKiBndrX kv)
                                    $ \kv' -> ZonkT $ \env' -> (k env' kv')
  , tm_tycon = \tc -> zonkTcTyConToTyCon tc
  , tm_mkcm = zonk_mkindmapper
  }

zonkTcTyConToTyCon :: AnyTyCon -> TcM (TyCon (TyVar KiVar) KiVar)
zonkTcTyConToTyCon tc@(TyCon {..})
  | isTcTyCon tc = do
      thing <- tcLookupGlobalOnly (getName tc)
      case thing of
        ATyCon real_tc -> return real_tc
        _ -> pprPanic "zonkTcTyCon" (ppr tc $$ ppr thing)
  | otherwise = do
      kind <- zonkTcKindToKind tyConKind
      let tc' = TyCon { tyConKind = kind, tyConNullaryTy = mkNakedTyConTy tc', .. }
      return tc'

zonkTcTypeToTypeX :: AnyType -> ZonkTcM (Type (TyVar KiVar) KiVar)
zonkTcTypesToTypesX :: [AnyType] -> ZonkTcM [Type (TyVar KiVar) KiVar]
(zonkTcTypeToTypeX, zonkTcTypesToTypesX) = case mapTypeX zonk_typemapper of
  (zty, ztys) -> (ZonkT . flip zty, ZonkT . flip ztys)

zonkKiVarOcc :: HasDebugCallStack => AnyKiVar -> ZonkTcM (MonoKind KiVar)
zonkKiVarOcc = handleAnyKv f_any f_tc
  where
    f_tc kv = do
      ZonkEnv { ze_kv_env = kv_env } <- getZonkEnv
      let lookup_in_kv_env :: ZonkTcM (MonoKind KiVar)
          lookup_in_kv_env = case lookupVarEnv_Directly kv_env (varUnique kv) of
            Nothing -> panic "zonkKiVarOcc bad skolem"
              -- return $ mkKiVarKi kv
            Just kv' -> return $ mkKiVarKi kv'
      
          finish_meta :: MonoKind KiVar -> ZonkTcM (MonoKind KiVar)
          finish_meta ki = do
            extendMetaKvEnv kv ki
            return ki
      
          zonk_meta
            :: TcRef (MetaDetails (AnyMonoKind))
            -> MetaDetails (AnyMonoKind)
            -> ZonkTcM (MonoKind KiVar)
          zonk_meta ref Flexi = do
            ki <- commitFlexiKv kv
            -- Not necessary to write, since we are adding to the ZonkEnv
            -- (also we can't write a MonoKind to a ref of AnyMonoKind)
            -- lift $ liftZonkM $ writeMetaKiVarRef kv ref ki
            finish_meta ki
      
          zonk_meta _ (Indirect ki) = do
            zki <- zonkTcMonoKindToMonoKindX ki
            finish_meta zki
      
      case tcVarDetails kv of
        SkolemVar {} -> lookup_in_kv_env
        MetaVar { mv_ref = ref } -> do
          mb_ki <- lookupMetaKv kv
          case mb_ki of
            Just ki -> return ki
            Nothing -> do mkv_details <- readTcRef ref
                          zonk_meta ref mkv_details

    f_any kv = return $ mkKiVarKi kv

extendMetaKvEnv :: TcKiVar -> MonoKind KiVar -> ZonkTcM ()
extendMetaKvEnv kv ki = ZonkT $ \ (ZonkEnv { ze_meta_kv_env = mkv_env_ref }) ->
  updTcRef mkv_env_ref (\env -> extendVarEnv env kv ki)

lookupMetaKv :: TcKiVar -> ZonkTcM (Maybe (MonoKind KiVar))
lookupMetaKv kv = ZonkT $ \ (ZonkEnv { ze_meta_kv_env = mkv_env_ref }) -> do
  mkv_env <- readTcRef mkv_env_ref
  return $ lookupVarEnv mkv_env kv

commitFlexiKv :: TcKiVar -> ZonkTcM (MonoKind KiVar)
commitFlexiKv kv = do
  flexi <- ze_flexi <$> getZonkEnv
  lift $ case flexi of
    NoFlexi -> pprPanic "NoFlexi" (ppr kv)

zonkKiCoVarOcc :: KiCoVar AnyKiVar -> ZonkTcM (KindCoercion KiVar)
zonkKiCoVarOcc cv = do
  ZonkEnv { ze_tv_env = tyco_env } <- getZonkEnv
  case lookupVarEnv_Directly tyco_env (varUnique cv) of
    Just cv' -> return $ mkKiCoVarCo cv'
    _ -> mkKiCoVarCo <$> (lift $ liftZonkM $ panic "zonkTyVarKind cv")

zonkKiCoHole :: KindCoercionHole AnyKiVar -> ZonkTcM (KindCoercion KiVar)
zonkKiCoHole hole@(KindCoercionHole { kch_ref = ref, kch_co_var = cv }) = do
  contents <- readTcRef ref
  case contents of
    Just co -> do
      co' <- zonkKiCoToCo co
      _ <- lift $ liftZonkM $ checkKiCoercionHole cv (asAnyKi co')
      return co'
    Nothing -> panic "zonkKiCoHole"

zonk_kindmapper :: KiCoMapper AnyKiVar KiVar ZonkEnv TcM
zonk_kindmapper = KiCoMapper
  { kcm_kibinder = \env kv k -> flip runZonkT env $ runZonkBndrT (zonkKiBndrX kv)
                               $ \kv' -> ZonkT $ \env' -> (k env' kv')
  , kcm_mkcm = zonk_mkindmapper
  }

zonk_mkindmapper :: MKiCoMapper AnyKiVar KiVar ZonkEnv TcM
zonk_mkindmapper = MKiCoMapper
  { mkcm_kivar = \env kv -> runZonkT (zonkKiVarOcc kv) env
  , mkcm_covar = \env cv -> runZonkT (zonkKiCoVarOcc cv) env
  , mkcm_hole = \env co -> runZonkT (zonkKiCoHole co) env
  }

zonkTcKindToKind :: AnyKind -> TcM (Kind KiVar)
zonkTcKindToKind ki = initZonkEnv NoFlexi $ zonkTcKindToKindX ki

zonkTcKindToKindX :: AnyKind -> ZonkTcM (Kind KiVar)
zonkTcKindsToKindsX :: [AnyKind] -> ZonkTcM [Kind KiVar]
(zonkTcKindToKindX, zonkTcKindsToKindsX) = case mapKindX zonk_kindmapper of
  (zki, zkis) -> (ZonkT . flip zki, ZonkT . flip zkis)

zonkTcMonoKindToMonoKindX :: AnyMonoKind -> ZonkTcM (MonoKind KiVar)
zonkTcMonoKindsToMonoKindsX :: [AnyMonoKind] -> ZonkTcM [MonoKind KiVar]
zonkKiCoToCo :: AnyKindCoercion -> ZonkTcM (KindCoercion KiVar)
(zonkTcMonoKindToMonoKindX, zonkTcMonoKindsToMonoKindsX, zonkKiCoToCo)
  = case mapMKiCoX zonk_mkindmapper of
      (zki, zkis, zco, _) ->
        (ZonkT . flip zki, ZonkT . flip zkis, ZonkT . flip zco)

zonkIdBndr :: AnyId -> ZonkTcM (Id (TyVar KiVar) KiVar)
zonkIdBndr = changeIdTypeM zonkTcTypeToTypeX

zonkTopDecls :: LCsBinds Tc -> TcM (TypeEnv, LCsBinds Tc)
zonkTopDecls binds
  = initZonkEnv NoFlexi
    $ runZonkBndrT (zonkRecMonoBinds binds) $ \binds' -> do
        ty_env <- panic "zonkEnvIds <$> getZonkEnv"
        return (ty_env, binds')

zonkRecMonoBinds :: LCsBinds Tc -> ZonkBndrTcM (LCsBinds Tc)
zonkRecMonoBinds binds = mfix $ \new_binds -> do
  extendIdZonkEnvRec (collectCsBindsBinders CollNoDictBinders new_binds)
  noBinders $ zonkMonoBinds binds

zonkMonoBinds :: LCsBinds Tc -> ZonkTcM (LCsBinds Tc)
zonkMonoBinds = mapM zonk_lbind

zonk_lbind :: LCsBind Tc -> ZonkTcM (LCsBind Tc)
zonk_lbind = wrapLocZonkMA zonk_bind

zonk_bind :: CsBind Tc -> ZonkTcM (CsBind Tc)

zonk_bind bind@(FunBind { fun_id = L loc var
                        , fun_body = body
                        , fun_ext = (co_fn, ticks) }) = do
  new_var <- zonkIdBndr var
  runZonkBndrT (zonkCoFn co_fn) $ \new_co_fn -> do

    panic "zonk_bind unfinished"

zonk_bind _ = panic "zonk_bind"

zonkCoFn :: CsWrapper -> ZonkBndrTcM CsWrapper
zonkCoFn = panic "zonkCoFn"
-- zonkCoFn
-- zonkCoFn

{- *********************************************************************
*                                                                      *
              Patterns
*                                                                      *
********************************************************************* -}

{- *********************************************************************
*                                                                      *
              Constraints and evidence
*                                                                      *
********************************************************************* -}

{- *********************************************************************
*                                                                      *
             Checking for coercion holes
*                                                                      *
********************************************************************* -}

unpackKiCoercionHole_maybe :: KindCoercionHole kv -> TcM (Maybe AnyKindCoercion)
unpackKiCoercionHole_maybe (KindCoercionHole { kch_ref = ref }) = readTcRef ref

zonkRewriterSet :: KiRewriterSet -> TcM KiRewriterSet
zonkRewriterSet (KiRewriterSet set) = nonDetStrictFoldUniqSet go (return emptyKiRewriterSet) set
  where
    --go :: KindCoercionHole -> TcM KiRewriterSet -> TcM KiRewriterSet
    go hole m_acc = unionKiRewriterSet <$> check_hole hole <*> m_acc

    --check_hole :: KindCoercionHole -> TcM KiRewriterSet
    check_hole hole = do
      m_co <- unpackKiCoercionHole_maybe hole
      case m_co of
        Nothing -> return $ unitKiRewriterSet hole
        Just co -> unUCHM (check_co co)

    -- check_ki :: MonoKind -> UnfilledCoercionHoleMonoid
    -- check_co :: KindCoercion -> UnfilledCoercionHoleMonoid
    (check_ki, _, check_co, _) = foldMonoKiCo folder ()

    --folder :: MKiCoFolder () UnfilledCoercionHoleMonoid
    folder = panic "folder"
      -- MKiCoFolder { kcf_kivar = \_ _ -> mempty
      --                    , kcf_covar = \_ cv -> check_ki (varKind cv)
      --                    , kcf_hole = \_ -> UCHM . check_hole }

newtype UnfilledCoercionHoleMonoid = UCHM { unUCHM :: TcM KiRewriterSet }

instance Semigroup UnfilledCoercionHoleMonoid where
  UCHM l <> UCHM r = UCHM (unionKiRewriterSet <$> l <*> r)

instance Monoid UnfilledCoercionHoleMonoid where
  mempty = UCHM (return emptyKiRewriterSet)

