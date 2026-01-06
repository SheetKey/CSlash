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
       , checkKiCoercionHole
       , checkTyCoercionHole )

import CSlash.Core.Type
import CSlash.Core.Type.Rep (mkNakedTyConTy, TypeCoercion, TypeCoercionHole(..))
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
import Data.List.NonEmpty (NonEmpty)

type ZonkTcM = ZonkT TcM

type ZonkBndrTcM = ZonkBndrT TcM

wrapLocZonkMA
  :: (a -> ZonkTcM b)
  -> GenLocated (EpAnn ann) a
  -> ZonkTcM (GenLocated (EpAnn ann) b)
wrapLocZonkMA fn (L loc a) = ZonkT $ \ze -> setSrcSpanA loc $ do
  b <- runZonkT (fn a) ze
  return (L loc b)

wrapLocZonkBndrMA
  :: (a -> ZonkBndrTcM b)
  -> GenLocated (EpAnn ann) a
  -> ZonkBndrTcM (GenLocated (EpAnn ann) b)
wrapLocZonkBndrMA fn (L loc a) = ZonkBndrT $ \k -> ZonkT $ \ze ->
  setSrcSpanA loc $ runZonkT (runZonkBndrT (fn a) $ \b -> k (L loc b)) ze

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
  updTcRef mtv_env_ref (\env -> extendVarEnv env tv ty)

lookupMetaTv :: TcTyVar AnyKiVar -> ZonkTcM (Maybe (Type (TyVar KiVar) KiVar))
lookupMetaTv tv = ZonkT $ \ (ZonkEnv { ze_meta_tv_env = mtv_env_ref }) -> do
  mtv_env <- readTcRef mtv_env_ref
  return $ lookupVarEnv mtv_env tv

commitFlexiTv :: TcTyVar AnyKiVar -> MonoKind KiVar -> ZonkTcM (Type (TyVar KiVar) KiVar)
commitFlexiTv tv zonked_kind = do
  flexi <- ze_flexi <$> getZonkEnv
  lift $ case flexi of
    NoFlexi -> pprPanic "NoFlexi" (ppr tv <+> colon <+> ppr zonked_kind) 
    DefaultFlexiKi -> pprPanic "DefaultFlexiKi" (ppr tv <+> colon <+> ppr zonked_kind)

zonkTyCoVarOcc
  :: TyCoVar (AnyTyVar AnyKiVar) AnyKiVar
  -> ZonkTcM (TypeCoercion (TyVar KiVar) KiVar)
zonkTyCoVarOcc cv = mkTyCoVarCo <$> (changeIdTypeM zonkTcTypeToTypeX cv)

zonkTyCoHole :: AnyTypeCoercionHole -> ZonkTcM (TypeCoercion (TyVar KiVar) KiVar)
zonkTyCoHole hole@(TypeCoercionHole { tch_ref = ref, tch_co_var = cv }) = do
  contents <- readTcRef ref
  case contents of
    Just co -> do co' <- zonkTyCoToTyCo co
                  _ <- lift $ liftZonkM $ checkTyCoercionHole cv (panic "asAnyTyKi co'")
                  return co'
    Nothing -> panic "zonkTyCoHole"

zonk_typemapper :: TyCoMapper (AnyTyVar AnyKiVar) AnyKiVar (TyVar KiVar) KiVar ZonkEnv TcM
zonk_typemapper = TyCoMapper
  { tm_tyvar = \env tv -> runZonkT (zonkTyVarOcc tv) env
  , tm_covar = \env cv -> runZonkT (zonkTyCoVarOcc cv) env
  , tm_hole = \env co -> runZonkT (zonkTyCoHole co) env
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
zonkTyCoToTyCo :: AnyTypeCoercion -> ZonkTcM (TypeCoercion (TyVar KiVar) KiVar)
(zonkTcTypeToTypeX, zonkTcTypesToTypesX, zonkTyCoToTyCo) = case mapTyCoX zonk_typemapper of
  (zty, ztys, zco, _) -> (ZonkT . flip zty, ZonkT . flip ztys, ZonkT . flip zco)

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
    DefaultFlexiKi -> do
      traceTc "Defaulting flexi kivar to Linear:" (ppr kv)
      return $ BIKi LKd

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

zonkEnvIds :: ZonkEnv -> TypeEnv
zonkEnvIds (ZonkEnv { ze_id_env = id_env })
  = mkNameEnv [(getName id, AnId id) | id <- nonDetEltsUFM id_env]

zonkIdOcc :: AnyId -> ZonkTcM ZkId
zonkIdOcc id
  | isLocalId id
  = do ZonkEnv { ze_id_env = id_env } <- getZonkEnv
       return $ lookupVarEnv_Directly id_env (varUnique id) `orElse` panic "zonkIdOcc"
  | otherwise
  = panic "return id" -- make a type mapper in maybe monad that does toTy/KiVar_maybe on vars

zonkIdBndrX :: AnyId -> ZonkBndrTcM ZkId
zonkIdBndrX v = do
  id <- noBinders $ zonkIdBndr v
  extendIdZonkEnv id
  return id
{-# INLINE zonkIdBndrX #-}

zonkIdBndr :: AnyId -> ZonkTcM ZkId
zonkIdBndr = changeIdTypeM zonkTcTypeToTypeX

zonkTopDecls :: LCsBinds Tc -> TcM (TypeEnv, LCsBinds Zk)
zonkTopDecls binds
  = initZonkEnv DefaultFlexiKi
    $ runZonkBndrT (zonkRecMonoBinds binds) $ \binds' -> do
        ty_env <- zonkEnvIds <$> getZonkEnv
        return (ty_env, binds')

zonkLocalBinds :: CsLocalBinds Tc -> ZonkBndrTcM (CsLocalBinds Zk)
zonkLocalBinds (EmptyLocalBinds x) = return $ EmptyLocalBinds x
zonkLocalBinds (CsValBinds _ (ValBinds {})) = panic "zonkLocalBind ValBinds"
zonkLocalBinds (CsValBinds x (XValBindsLR (NValBinds binds sigs))) = do
  new_binds <- traverse go binds
  return $ CsValBinds x (XValBindsLR (NValBinds new_binds sigs))
  where
    go (r, b) = do
      b' <- zonkRecMonoBinds b
      return (r, b')

zonkRecMonoBinds :: LCsBinds Tc -> ZonkBndrTcM (LCsBinds Zk)
zonkRecMonoBinds binds = mfix $ \new_binds -> do
  extendIdZonkEnvRec (collectCsBindsBinders CollNoDictBinders new_binds)
  noBinders $ zonkMonoBinds binds

zonkMonoBinds :: LCsBinds Tc -> ZonkTcM (LCsBinds Zk)
zonkMonoBinds = mapM zonk_lbind

zonk_lbind :: LCsBind Tc -> ZonkTcM (LCsBind Zk)
zonk_lbind = wrapLocZonkMA zonk_bind

zonk_bind :: CsBind Tc -> ZonkTcM (CsBind Zk)

zonk_bind bind@(FunBind { fun_id = L loc var
                        , fun_body = body
                        , fun_ext = (co_fn, ticks) }) = do
  new_var <- zonkIdBndr var
  runZonkBndrT (zonkCoFn co_fn) $ \new_co_fn -> do

    panic "zonk_bind unfinished"

zonk_bind bind@(TyFunBind {}) = panic "zonk_bind TyFunBind"

zonk_bind bind@(TCVarBind {}) = panic "zonk_bind TCVarBind"

zonk_bind (XCsBindsLR (AbsBinds { abs_tvs = tyvars
                                , abs_exports = exports
                                , abs_binds = val_binds
                                , abs_sig = has_sig }))
  = assertPpr (null tyvars) (text "zonk_bind/AbsBinds has nonempty tyvars") $ do
  (new_val_bind, new_exports) <- mfix $ \ ~(new_val_binds, _) ->
    runZonkBndrT (extendIdZonkEnvRec $ collectCsBindsBinders CollNoDictBinders new_val_binds)
    $ \_ -> do new_val_binds <- mapM zonk_val_bind val_binds
               new_exports <- mapM zonk_export exports
               return (new_val_binds, new_exports)
  return $ XCsBindsLR $ AbsBinds { abs_tvs = tyvars
                                 , abs_exports = new_exports
                                 , abs_binds = new_val_bind
                                 , abs_sig = has_sig }
  where
    zonk_val_bind lbind
      | has_sig
      , (L loc (FunBind { fun_id = (L mloc mono_id)
                        , fun_body = body
                        , fun_ext = (co_fn, ticks) })) <- lbind
      = do new_mono_id <- changeIdTypeM zonkTcTypeToTypeX mono_id
           runZonkBndrT (zonkCoFn co_fn) $ \new_co_fn -> do
             new_body <- zonkLExpr body
             return $ L loc $ FunBind { fun_id = L mloc new_mono_id
                                      , fun_body = new_body
                                      , fun_ext = (new_co_fn, ticks) }
      | otherwise
      = zonk_lbind lbind

    zonk_export :: ABExport Tc -> ZonkTcM (ABExport Zk)
    zonk_export (ABE { abe_poly = poly_id, abe_mono = mono_id }) = do
      new_poly_id <- zonkIdBndr poly_id
      new_mono_id <- zonkIdOcc mono_id
      return $ ABE { abe_poly = new_poly_id
                   , abe_mono = new_mono_id }

{- *********************************************************************
*                                                                      *
              Match group
*                                                                      *
********************************************************************* -}

zonkMatchGroup
  :: ( Anno (GRHS Tc (LocatedA (body Tc))) ~ EpAnnCO
     , Anno (GRHS Tc (LocatedA (body Tc))) ~ Anno (GRHS Zk (LocatedA (body Zk)))
     , Anno (Match Tc (LocatedA (body Tc))) ~ Anno (Match Zk (LocatedA (body Zk)))
     , Anno [LMatch Tc (LocatedA (body Tc))] ~ Anno [LMatch Zk (LocatedA (body Zk))]
     )
  => (LocatedA (body Tc) -> ZonkTcM (LocatedA (body Zk)))
  -> MatchGroup Tc (LocatedA (body Tc))
  -> ZonkTcM (MatchGroup Zk (LocatedA (body Zk)))
zonkMatchGroup zBody (MG { mg_alts = L l ms, mg_ext = MatchGroupTc arg_tys res_ty origin }) = do
  ms' <- mapM (zonkMatch zBody) ms
  arg_tys' <- zonkTcTypesToTypesX arg_tys
  res_ty' <- zonkTcTypeToTypeX res_ty
  return $ MG { mg_alts = L l ms'
              , mg_ext = MatchGroupZk arg_tys' res_ty' origin }

zonkMatch
  :: ( Anno (GRHS Tc (LocatedA (body Tc))) ~ EpAnnCO
     , Anno (GRHS Tc (LocatedA (body Tc))) ~ Anno (GRHS Zk (LocatedA (body Zk)))
     , Anno (Match Tc (LocatedA (body Tc))) ~ Anno (Match Zk (LocatedA (body Zk))) )
  => (LocatedA (body Tc) -> ZonkTcM (LocatedA (body Zk)))
  -> LMatch Tc (LocatedA (body Tc))
  -> ZonkTcM (LMatch Zk (LocatedA (body Zk)))
zonkMatch zBody (L loc match@(Match { m_pats = L l pats
                                    , m_grhss = grhss })) = 
  runZonkBndrT (zonkPats pats) $ \ new_pats -> do
    new_grhss <- zonkGRHSs zBody grhss
    return (L loc (match { m_pats = L l new_pats, m_grhss = new_grhss }))

zonkGRHSs
  :: ( Anno (GRHS Tc (LocatedA (body Tc))) ~ EpAnnCO
     , Anno (GRHS Tc (LocatedA (body Tc))) ~ Anno (GRHS Zk (LocatedA (body Zk))) )
  => (LocatedA (body Tc) -> ZonkTcM (LocatedA (body Zk)))
  -> GRHSs Tc (LocatedA (body Tc))
  -> ZonkTcM (GRHSs Zk (LocatedA (body Zk)))
zonkGRHSs zBody (GRHSs x grhss) = do
  new_grhss <- mapM (wrapLocZonkMA zonk_grhs) grhss
  return (GRHSs x new_grhss)
  where
    zonk_grhs (GRHS xx guarded rhs)
      = runZonkBndrT (zonkStmts zonkLExpr guarded) $ \ new_guarded ->
          GRHS xx new_guarded <$> zBody rhs

{- *********************************************************************
*                                                                      *
              CsExpr
*                                                                      *
********************************************************************* -}

zonkLExpr :: LCsExpr Tc -> ZonkTcM (LCsExpr Zk)
zonkLExpr expr = wrapLocZonkMA zonkExpr expr

zonkExpr :: CsExpr Tc -> ZonkTcM (CsExpr Zk)

zonkExpr (CsVar x (L l id))
  = assertPpr (isNothing (isDataConId_maybe id)) (ppr id) $ do
  id' <- zonkIdOcc id
  return (CsVar x (L l id'))

zonkExpr (CsUnboundVar x _) = dataConCantHappen x

zonkExpr (CsLit x lit) = panic "return (CsLit x lit)"

zonkExpr (CsOverLit x lit) = do
  lit' <- zonkOverLit lit
  return (CsOverLit x lit')

zonkExpr (CsLam x matches) = do
  new_matches <- zonkMatchGroup zonkLExpr matches
  return (CsLam x new_matches)

zonkExpr (CsTyLam x matches) = do
  new_matches <- zonkMatchGroup zonkLExpr matches
  return (CsTyLam x new_matches)

zonkExpr (CsApp x e1 e2) = do
  new_e1 <- zonkLExpr e1
  new_e2 <- zonkLExpr e2
  return $ CsApp x new_e1 new_e2

zonkExpr (XExpr (WrapExpr co_fn expr))
  = runZonkBndrT (zonkCoFn co_fn) $ \new_co_fn -> do
      new_expr <- zonkExpr expr
      return (XExpr (WrapExprZk new_co_fn new_expr))

zonkExpr (XExpr (ExpandedThingTc thing expr)) = do
  new_expr <- zonkExpr expr
  return $ XExpr (ExpandedThingZk thing new_expr)

zonkExpr (XExpr (ConLikeTc con)) = return $ XExpr $ ConLikeZk con

zonkExpr other = pprPanic "zonkExpr" (ppr other)

zonkCoFn :: AnyCsWrapper -> ZonkBndrTcM ZkCsWrapper
zonkCoFn WpHole = return WpHole
zonkCoFn (WpCompose c1 c2) = do
  c1' <- zonkCoFn c1
  c2' <- zonkCoFn c2
  return (WpCompose c1' c2')
zonkCoFn (WpFun c2 fki t1) = do
  c2' <- zonkCoFn c2
  fki' <- noBinders $ zonkTcMonoKindToMonoKindX fki
  t1' <- noBinders $ zonkTcTypeToTypeX t1
  return (WpFun c2' fki' t1')
zonkCoFn (WpCast co) = WpCast <$> noBinders (zonkTyCoToTyCo co)
zonkCoFn (WpTyLam tv) = assert (handleAnyTv (const True) isImmutableVar tv) $
                        WpTyLam <$> zonkTyBndrX tv
zonkCoFn (WpKiLam kv) = assert (handleAnyKv (const True) isImmutableVar kv) $
                        WpKiLam <$> zonkKiBndrX kv
zonkCoFn (WpTyApp ty) = WpTyApp <$> noBinders (zonkTcTypeToTypeX ty)
zonkCoFn (WpKiApp ki) = WpKiApp <$> noBinders (zonkTcMonoKindToMonoKindX ki)
zonkCoFn (WpKiCoApp kco) = WpKiCoApp <$> noBinders (zonkKiCoToCo kco)
zonkCoFn (WpMultCoercion co) = WpMultCoercion <$> noBinders (zonkKiCoToCo co)

zonkOverLit :: CsOverLit Tc -> ZonkTcM (CsOverLit Zk)
zonkOverLit = panic "zonkOverLit"

zonkStmts
  :: ( Anno (StmtLR Tc Tc (LocatedA (body Tc))) ~ SrcSpanAnnA
     , Anno (StmtLR Tc Tc (LocatedA (body Tc))) ~ Anno (StmtLR Zk Zk (LocatedA (body Zk))) )
  => (LocatedA (body Tc) -> ZonkTcM (LocatedA (body Zk)))
  -> [LStmt Tc (LocatedA (body Tc))]
  -> ZonkBndrTcM [LStmt Zk (LocatedA (body Zk))]
zonkStmts _ [] = return []
zonkStmts zBody (s:ss) = do
  s' <- wrapLocZonkBndrMA (zonkStmt zBody) s
  ss' <- zonkStmts zBody ss
  return (s' : ss')

zonkStmt
  :: ( Anno (StmtLR Tc Tc (LocatedA (body Tc))) ~ SrcSpanAnnA
     , Anno (StmtLR Tc Tc (LocatedA (body Tc))) ~ Anno (StmtLR Zk Zk (LocatedA (body Zk))) )
  => (LocatedA (body Tc) -> ZonkTcM (LocatedA (body Zk)))
  -> Stmt Tc (LocatedA (body Tc))
  -> ZonkBndrTcM (Stmt Zk (LocatedA (body Zk)))

zonkStmt zBody (BodyStmt ty body) = do
  new_body <- noBinders $ zBody body
  new_ty <- noBinders $ zonkTcTypeToTypeX ty
  return $ BodyStmt new_ty new_body

zonkStmt _ (LetStmt x binds) = LetStmt x <$> zonkLocalBinds binds

zonkStmt zBody (BindStmt x pat body) = do
  new_body <- noBinders $ zBody body
  new_pat <- zonkPat pat
  return $ BindStmt x new_pat new_body

{- *********************************************************************
*                                                                      *
              Patterns
*                                                                      *
********************************************************************* -}

zonkPat :: LPat Tc -> ZonkBndrTcM (LPat Zk)
zonkPat pat = wrapLocZonkBndrMA zonk_pat pat

zonk_pat :: Pat Tc -> ZonkBndrTcM (Pat Zk)

zonk_pat (ParPat x p) = do
  p' <- zonkPat p
  return (ParPat x p')
  
zonk_pat (WildPat ty) = return (WildPat ty)

zonk_pat (VarPat x (L l v)) = do
  v' <- zonkIdBndrX v
  return (VarPat x (L l v'))
  
zonk_pat (AsPat x (L loc v) pat) = do
  v' <- zonkIdBndrX v
  pat' <- zonkPat pat
  return (AsPat x (L loc v') pat')

zonk_pat (TuplePat tys pats) = do
  pats' <- zonkPats pats
  return (TuplePat tys pats')

zonk_pat (SumPat tys pat alt arity) = do
  pat' <- zonkPat pat
  return (SumPat tys pat' alt arity)

zonk_pat (ConPat {}) = panic "zonk ConPat"

zonk_pat (LitPat x lit) = return $ panic "LitPat x lit"

zonk_pat (SigPat ty pat cs_ty) = do
  ty' <- noBinders $ zonkTcTypeToTypeX ty
  pat' <- zonkPat pat
  return $ SigPat ty' pat' cs_ty

zonk_pat (NPat ty (L l lit) mb_new eq_expr) = panic "zonk NPat"

zonk_pat _ = panic "zonk_pat"

zonkPats :: Traversable f => f (LPat Tc) -> ZonkBndrTcM (f (LPat Zk))
zonkPats = traverse zonkPat
{-# SPECIALIZE zonkPats :: [LPat Tc] -> ZonkBndrTcM [LPat Zk] #-}
{-# SPECIALIZE zonkPats :: NonEmpty (LPat Tc) -> ZonkBndrTcM (NonEmpty (LPat Zk)) #-}

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

unpackTyCoercionHole_maybe :: TypeCoercionHole tv kv -> TcM (Maybe AnyTypeCoercion)
unpackTyCoercionHole_maybe (TypeCoercionHole { tch_ref = ref }) = readTcRef ref

unpackKiCoercionHole_maybe :: KindCoercionHole kv -> TcM (Maybe AnyKindCoercion)
unpackKiCoercionHole_maybe (KindCoercionHole { kch_ref = ref }) = readTcRef ref

zonkTyRewriterSet :: TyRewriterSet -> TcM TyRewriterSet
zonkTyRewriterSet (TyRewriterSet set)
  = nonDetStrictFoldUniqSet go (return emptyTyRewriterSet) set
  where
    go hole m_acc = unionTyRewriterSet <$> check_hole hole <*> m_acc

    check_hole hole = do
      m_co <- unpackTyCoercionHole_maybe hole
      case m_co of
        Nothing -> return $ unitTyRewriterSet hole
        Just co -> panic "unUCHM (check_co co)"

    check_co = panic "check_co"

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

