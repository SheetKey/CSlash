{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Core.Kind where

import CSlash.Types.Var

import CSlash.Utils.Outputable

import qualified Data.Data as Data

{- **********************************************************************
*                                                                       *
                        Kind
*                                                                       *
********************************************************************** -}

data Kind
  = KdVarKd Var
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
pprKind = undefined

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
  KdVarKd _ -> True
  FunKd _ k1 k2 -> noFreeVarsOfKind k1 || noFreeVarsOfKind k2
  -- LTKd k1 k2 -> noFreeVarsOfKind k1 || noFreeVarsOfKind k2
  -- LTEQKd k1 k2 -> noFreeVarsOfKind k1 || noFreeVarsOfKind k2
  _ -> False

{- *********************************************************************
*                                                                      *
                foldKind
*                                                                      *
********************************************************************* -}

data KindFolder env a = KindFolder
  { kf_view :: Kind -> Maybe Kind
  , kf_kdvar :: env -> KindVar -> a
  , kf_UKd :: a
  , kf_AKd :: a
  , kf_LKd :: a
  , kd_ctxt :: env -> [KdRel] -> a
  }

{-# INLINE foldKind #-}
foldKind :: Monoid a => KindFolder env a -> env -> (Kind -> a, [Kind] -> a)
foldKind (KindFolder { kf_view = view
                     , kf_kdvar = kdvar
                     , ..
                     }) env
  = (go_kd env, go_kds env)
  where
    go_kd env kd | Just kd' <- view kd = go_kd env kd'
    go_kd env (KdVarKd kv) = kdvar env kv
    go_kd env (FunKd FKF_K_K arg res) = go_kd env arg `mappend` go_kd env res
    go_kd env (FunKd FKF_C_K ctxt inner) = go_kd env ctxt `mappend` go_kd env inner
    go_kd env (KdContext rels) = kd_ctxt env rels
    go_kd _ UKd = kf_UKd
    go_kd _ AKd = kf_AKd
    go_kd _ LKd = kf_LKd

    go_kds _ [] = mempty
    go_kds env (k:ks) = go_kd env k `mappend` go_kds env ks

noKindView :: Kind -> Maybe Kind
noKindView _ = Nothing
