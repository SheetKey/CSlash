{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Core.Kind where

import CSlash.Types.Var

import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import qualified Data.Data as Data

{- **********************************************************************
*                                                                       *
                        Kind
*                                                                       *
********************************************************************** -}

data Kind
  = KiVarKi Var
  | UKd
  | AKd
  | LKd
  | FunKd
    { fk_af :: FunKdFlag
    , kft_arg :: Kind
    , kft_res :: Kind
    }
  | KdContext [KdRel]
  --  | LTKd Kind Kind
  --  | LTEQKd Kind Kind
  deriving (Eq, Data.Data)

data KdRel
  = LTKd Kind Kind
  | LTEQKd Kind Kind
  deriving (Eq, Data.Data)

instance Outputable Kind where
  ppr = pprKind

pprKind :: Kind -> SDoc
pprKind _ = text "{pprKind not defined}"

data FunKdFlag
  = FKF_K_K -- Kind -> Kind
  | FKF_C_K -- Context -> Kind            -- IGNORE TO RIGHT   -- LT/LTEQ -> Kind
--  | FKF_C_C -- LT/LTEQ -> LT/LTEQ
  deriving (Eq, Data.Data)

instance Outputable FunKdFlag where
  ppr FKF_K_K = text "[->]"
  ppr FKF_C_K = text "[=>]"
--  ppr FKF_C_C = text "[==>]"

-- is constraint kind
isCKind :: Kind -> Bool
-- isCKind (LTKd _ _) = True
-- isCKind (LTEQKd _ _) = True
isCKind (KdContext _) = True
isCKind _ = False

-- 'noFreeVarsOfType' in GHC
noFreeVarsOfKind :: Kind -> Bool
noFreeVarsOfKind k = case k of
  KiVarKi _ -> True
  FunKd _ k1 k2 -> noFreeVarsOfKind k1 || noFreeVarsOfKind k2
  -- LTKd k1 k2 -> noFreeVarsOfKind k1 || noFreeVarsOfKind k2
  -- LTEQKd k1 k2 -> noFreeVarsOfKind k1 || noFreeVarsOfKind k2
  _ -> False

{- **********************************************************************
*                                                                       *
            Simple constructors
*                                                                       *
********************************************************************** -}

mkKiVarKi :: KindVar -> Kind
mkKiVarKi v = assertPpr (isKiVar v) (ppr v) $ KiVarKi v

{- *********************************************************************
*                                                                      *
                foldKind
*                                                                      *
********************************************************************* -}

data KindFolder env a = KindFolder
  { kf_view :: Kind -> Maybe Kind
  , kf_kivar :: env -> KindVar -> a
  , kf_UKd :: a
  , kf_AKd :: a
  , kf_LKd :: a
  , kf_ctxt :: env -> [KdRel] -> a
  }

{-# INLINE foldKind #-}
foldKind :: Monoid a => KindFolder env a -> env -> (Kind -> a, [Kind] -> a)
foldKind (KindFolder { kf_view = view
                     , kf_kivar = kivar
                     , ..
                     }) env
  = (go_kd env, go_kds env)
  where
    go_kd env kd | Just kd' <- view kd = go_kd env kd'
    go_kd env (KiVarKi kv) = kivar env kv
    go_kd env (FunKd FKF_K_K arg res) = go_kd env arg `mappend` go_kd env res
    go_kd env (FunKd FKF_C_K ctxt inner) = go_kd env ctxt `mappend` go_kd env inner
    go_kd env (KdContext rels) = kf_ctxt env rels
    go_kd _ UKd = kf_UKd
    go_kd _ AKd = kf_AKd
    go_kd _ LKd = kf_LKd

    go_kds _ [] = mempty
    go_kds env (k:ks) = go_kd env k `mappend` go_kds env ks

noKindView :: Kind -> Maybe Kind
noKindView _ = Nothing

{- *********************************************************************
*                                                                      *
                mapKind
*                                                                      *
********************************************************************* -}

data KindMapper env m = KindMapper
  { km_kivar :: env -> KindVar -> m Kind
  , km_UKd :: env -> m Kind
  , km_AKd :: env -> m Kind
  , km_LKd :: env -> m Kind
  }

{-# INLINE mapKind #-}
mapKind :: Monad m => KindMapper () m -> (Kind -> m Kind, [Kind] -> m [Kind])
mapKind mapper = case mapKindX mapper of
                   (go_ki, go_kis) -> (go_ki (), go_kis ())

{-# INLINE mapKindX #-}
mapKindX :: Monad m => KindMapper env m -> (env -> Kind -> m Kind, env -> [Kind] -> m [Kind])
mapKindX (KindMapper { km_kivar = kivar
                     , km_UKd = ukd
                     , km_AKd = akd
                     , km_LKd = lkd })
  = (go_ki, go_kis)
  where
    go_kis !_ [] = return []
    go_kis !env (ki:kis) = (:) <$> go_ki env ki <*> go_kis env kis

    go_ki !env (KiVarKi kv) = kivar env kv
    go_ki !env UKd = ukd env
    go_ki !env AKd = akd env
    go_ki !env LKd = lkd env
    go_ki !env ki@(FunKd _ arg res) = do
      arg' <- go_ki env arg
      res' <- go_ki env res
      return ki { kft_arg = arg', kft_res = res' }
    go_ki !env (KdContext rels) = KdContext <$> traverse (go_rel env) rels

    go_rel !env (LTKd k1 k2) = do
      k1' <- go_ki env k1 
      k2' <- go_ki env k2
      return $ LTKd k1' k2'
    go_rel !env (LTEQKd k1 k2) = do
      k1' <- go_ki env k1 
      k2' <- go_ki env k2
      return $ LTKd k1' k2'
