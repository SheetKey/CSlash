{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Core.Kind where

import Prelude hiding ((<>))

import CSlash.Types.Var
import CSlash.Types.Var.Env

import CSlash.Types.Basic
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
  deriving Data.Data

data KdRel
  = LTKd Kind Kind
  | LTEQKd Kind Kind
  deriving Data.Data

instance Outputable KdRel where
  ppr (LTKd k1 k2) = ppr k1 <+> text "<" <+> ppr k2
  ppr (LTEQKd k1 k2) = ppr k1 <+> text "<=" <+> ppr k2

instance Outputable Kind where
  ppr = pprKind

addKindContext :: [KdRel] -> Kind -> Kind
addKindContext [] ki = ki
addKindContext ctxt (FunKd FKF_C_K (KdContext og_ctxt) ki)
  = FunKd FKF_C_K (KdContext (ctxt ++ og_ctxt)) ki
addKindContext ctxt ki = FunKd FKF_C_K (KdContext ctxt) ki

pprKind :: Kind -> SDoc
pprKind = pprPrecKind topPrec

pprPrecKind :: PprPrec -> Kind -> SDoc
pprPrecKind = pprPrecKindX emptyTidyEnv

pprPrecKindX :: TidyEnv -> PprPrec -> Kind -> SDoc
pprPrecKindX env prec ki
  = getPprStyle $ \sty ->
    getPprDebug $ \debug ->
    if debug
    then debug_ppr_ki prec ki
    else text "{pprKind not implemented}"--pprPrecIfaceKind prec (tidyToIfaceKindStyX env ty sty)

debugPprKind :: Kind -> SDoc
debugPprKind ki = debug_ppr_ki topPrec ki

debug_ppr_ki :: PprPrec -> Kind -> SDoc
debug_ppr_ki _ (KiVarKi kv) = ppr kv
debug_ppr_ki _ UKd = uKindLit
debug_ppr_ki _ AKd = aKindLit
debug_ppr_ki _ LKd = lKindLit
debug_ppr_ki prec (FunKd { fk_af = af, kft_arg = arg, kft_res = res })
  = maybeParen prec funPrec
    $ sep [ debug_ppr_ki funPrec arg, fun_arrow <+> debug_ppr_ki prec res]
  where
    fun_arrow = case af of
                  FKF_C_K -> darrow
                  FKF_K_K -> arrow
debug_ppr_ki prec (KdContext rels) = pprKdRels prec rels

pprKdRels :: PprPrec -> [KdRel] -> SDoc
pprKdRels _ [] = panic "pprKdRels []"
pprKdRels prec [rel] = pprKdRel prec rel
pprKdRels prec (rel:rels) = parens $ sep $ pprKdRel prec rel
                                           : (((text ", " <>) . pprKdRel prec) <$> rels)

pprKdRel :: PprPrec -> KdRel -> SDoc
pprKdRel prec (LTKd k1 k2) = sep [debug_ppr_ki prec k1, text "<", debug_ppr_ki prec k2]
pprKdRel prec (LTEQKd k1 k2) = sep [debug_ppr_ki prec k1, text "<=", debug_ppr_ki prec k2]

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

isFunKi :: Kind -> Bool
isFunKi (FunKd {}) = True
isFunKi _ = False

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

mkFunKi :: Kind -> Kind -> Kind
mkFunKi k1@(KdContext _) _ = pprPanic "mkFunKi" (ppr k1)
mkFunKi _ k2@(KdContext _) = pprPanic "mkFunKi" (ppr k2)
mkFunKi (FunKd FKF_C_K (KdContext c1) k1) (FunKd FKF_C_K (KdContext c2) k2)
  = FunKd FKF_C_K (KdContext (c1 ++ c2)) $ FunKd FKF_K_K k1 k2
mkFunKi (FunKd FKF_C_K c1 k1) k2
  = FunKd FKF_C_K c1 $ FunKd FKF_K_K k1 k2
mkFunKi k1 (FunKd FKF_C_K c2 k2)
  = FunKd FKF_C_K c2 $ FunKd FKF_K_K k1 k2
mkFunKi k1 k2 = FunKd FKF_K_K k1 k2    

mkFunKis :: [Kind] -> Kind -> Kind
mkFunKis = flip (foldr mkFunKi)

mkContextKi :: Kind -> Kind -> Kind
mkContextKi k1@(KdContext c1) k2 = case k2 of
  FunKd FKF_C_K (KdContext c2) k2' -> FunKd FKF_C_K (KdContext (c1 ++ c2)) k2'
  _ -> FunKd FKF_C_K k1 k2
mkContextKi k1 _ = pprPanic "mkContextKi" (ppr k1)

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
      return $ LTEQKd k1' k2'

{- *********************************************************************
*                                                                      *
                      KiVarKi
*                                                                      *
********************************************************************* -}

getKiVar_maybe :: Kind -> Maybe KindVar
getKiVar_maybe (KiVarKi kv) = Just kv
getKiVar_maybe _ = Nothing

{- *********************************************************************
*                                                                      *
                      FunKd
*                                                                      *
********************************************************************* -}

{-# INLINE splitFunKi_maybe #-}
splitFunKi_maybe :: Kind -> Maybe (Kind, Kind)
splitFunKi_maybe ki = case ki of
  FunKd FKF_C_K c ki -> case splitFunKi_maybe ki of
                               Nothing -> Nothing
                               Just (k1, k2) -> Just (FunKd FKF_C_K c k1, FunKd FKF_C_K c k2)
  FunKd FKF_K_K k1 k2 -> Just (k1, k2)
  _ -> Nothing
