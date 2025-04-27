{-# LANGUAGE RankNTypes #-}
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
  = ForAllKi {-# UNPACK #-} !KindVar Kind
  | Mono MonoKind
  deriving Data.Data

data MonoKind
  = KiVarKi Var
  | KiConApp KiCon [MonoKind]
  | FunKi
    { fk_f :: FunKiFlag
    , fk_arg :: MonoKind
    , fk_res :: MonoKind
    }
  deriving Data.Data

data KiCon
  = UKd
  | AKd
  | LKd
  | LTKi
  | LTEQKi
  deriving (Eq, Data.Data)

instance Outputable Kind where
  ppr = pprKind

instance Outputable MonoKind where
  ppr = pprMonoKind

pprKind :: Kind -> SDoc
pprKind = pprPrecKind topPrec

pprMonoKind :: MonoKind -> SDoc
pprMonoKind = pprPrecMonoKind topPrec

pprPrecKind :: PprPrec -> Kind -> SDoc
pprPrecKind = pprPrecKindX emptyTidyEnv

pprPrecMonoKind :: PprPrec -> MonoKind -> SDoc
pprPrecMonoKind = pprPrecMonoKindX emptyTidyEnv

pprPrecKindX :: TidyEnv -> PprPrec -> Kind -> SDoc
pprPrecKindX env prec ki
  = getPprStyle $ \sty ->
    getPprDebug $ \debug ->
    if debug
    then debug_ppr_ki prec ki
    else text "{pprKind not implemented}"--pprPrecIfaceKind prec (tidyToIfaceKindStyX env ty sty)

pprPrecMonoKindX :: TidyEnv -> PprPrec -> MonoKind -> SDoc
pprPrecMonoKindX env prec ki
  = getPprStyle $ \sty ->
    getPprDebug $ \debug ->
    if debug
    then debug_ppr_mono_ki prec ki
    else text "{pprKind not implemented}"--pprPrecIfaceKind prec (tidyToIfaceKindStyX env ty sty)

debugPprKind :: Kind -> SDoc
debugPprKind ki = debug_ppr_ki topPrec ki

debug_ppr_ki :: PprPrec -> Kind -> SDoc
debug_ppr_ki prec (Mono ki) = debug_ppr_mono_ki prec ki
debug_ppr_ki prec ki
  | (bndrs, body) <- splitForAllKiVars ki
  , not (null bndrs)
  = maybeParen prec funPrec $ sep [ text "forall" <+> fsep (map (braces . ppr) bndrs) <> dot
                                  , ppr body ]
debug_ppr_ki _ _ = panic "debug_ppr_ki unreachable"

debug_ppr_mono_ki :: PprPrec -> MonoKind -> SDoc
debug_ppr_mono_ki _ (KiVarKi kv) = ppr kv
debug_ppr_mono_ki prec ki@(KiConApp kc args)
  | UKd <- kc
  , [] <- args
  = uKindLit
  | AKd <- kc
  , [] <- args
  = aKindLit
  | LKd <- kc
  , [] <- args
  = lKindLit
  | LTKi <- kc
  , [k1, k2] <- args
  = maybeParen prec appPrec
    $ debug_ppr_mono_ki appPrec k1 <+> text "<" <+> debug_ppr_mono_ki appPrec k2
  | LTEQKi <- kc
  , [k1, k2] <- args
  = debug_ppr_mono_ki prec k1 <+> text "<" <+> debug_ppr_mono_ki prec k2
  | otherwise
  = panic "debug_ppr_ki" 

debug_ppr_mono_ki prec (FunKi { fk_f = f, fk_arg = arg, fk_res = res })
  = maybeParen prec funPrec
    $ sep [ debug_ppr_mono_ki funPrec arg, fun_arrow <+> debug_ppr_mono_ki prec res]
  where
    fun_arrow = case f of
                  FKF_C_K -> darrow
                  FKF_K_K -> arrow


data FunKiFlag
  = FKF_K_K -- Kind -> Kind
  | FKF_C_K -- Constraint -> Kind
  deriving (Eq, Data.Data)

instance Outputable FunKiFlag where
  ppr FKF_K_K = text "[->]"
  ppr FKF_C_K = text "[=>]"

{- **********************************************************************
*                                                                       *
            Simple constructors
*                                                                       *
********************************************************************** -}

mkKiVarKi :: KindVar -> Kind
mkKiVarKi v = assertPpr (isKiVar v) (ppr v) $ Mono $ KiVarKi v

mkKiVarMKi :: KindVar -> MonoKind
mkKiVarMKi v = assertPpr (isKiVar v) (ppr v) $ KiVarKi v

mkFunKi :: FunKiFlag -> MonoKind -> MonoKind -> MonoKind
mkFunKi f arg res = assertPpr (f == chooseFunKiFlag arg res)
                    (vcat [ text "f" <+> ppr f
                          , text "chooseF" <+> ppr (chooseFunKiFlag arg res)
                          , text "arg" <+> ppr arg
                          , text "res" <+> ppr res ])
                    $ FunKi { fk_f = f, fk_arg = arg, fk_res = res }

mkForAllKi :: KindVar -> Kind -> Kind
mkForAllKi v k = assertPpr (isKiVar v) (ppr v) $ ForAllKi v k

{- *********************************************************************
*                                                                      *
                foldKind
*                                                                      *
********************************************************************* -}

data KindFolder env a = KindFolder
  { kf_view :: Kind -> Maybe Kind
  , kf_kivar :: env -> KindVar -> a
  , kf_kibinder :: env -> TypeVar -> env
  }

{-# INLINE foldKind #-}
foldKind :: Monoid a => KindFolder env a -> env -> (Kind -> a, [Kind] -> a)
foldKind (KindFolder { kf_view = view
                     , kf_kivar = kivar
                     , kf_kibinder = kibinder
                     }) env
  = (go_kd env, go_kds env)
  where
    go_kd env kd | Just kd' <- view kd = go_kd env kd'
    go_kd env (Mono ki) = go_mono_kd env ki
    go_kd env (ForAllKi kv inner)
      = let !env' = kibinder env kv
        in go_kd env' inner

    go_mono_kd env (KiVarKi kv) = kivar env kv
    go_mono_kd env (FunKi _ arg res) = go_mono_kd env arg `mappend` go_mono_kd env res
    go_mono_kd env (KiConApp _ kis) = go_mono_kds env kis

    go_kds _ [] = mempty
    go_kds env (k:ks) = go_kd env k `mappend` go_kds env ks

    go_mono_kds _ [] = mempty
    go_mono_kds env (k:ks) = go_mono_kd env k `mappend` go_mono_kds env ks

noKindView :: Kind -> Maybe Kind
noKindView _ = Nothing

{- *********************************************************************
*                                                                      *
                mapKind
*                                                                      *
********************************************************************* -}

data KindMapper env m = KindMapper
  { km_kivar :: env -> KindVar -> m MonoKind
  , km_kibinder :: forall r. env -> KindVar -> (env -> KindVar -> m r) -> m r
  }

{-# INLINE mapKind #-}
mapKind :: Monad m => KindMapper () m -> (Kind -> m Kind, [Kind] -> m [Kind])
mapKind mapper = case mapKindX mapper of
                   (go_ki, go_kis) -> (go_ki (), go_kis ())

{-# INLINE mapKindX #-}
mapKindX :: Monad m => KindMapper env m -> (env -> Kind -> m Kind, env -> [Kind] -> m [Kind])
mapKindX (KindMapper { km_kivar = kivar, km_kibinder = kibinder })
  = (go_ki, go_kis)
  where
    go_kis !_ [] = return []
    go_kis !env (ki:kis) = (:) <$> go_ki env ki <*> go_kis env kis

    go_mono_kis !_ [] = return []
    go_mono_kis !env (ki:kis) = (:) <$> go_mono_ki env ki <*> go_mono_kis env kis

    go_ki !env (Mono ki) = do
      ki' <- go_mono_ki env ki
      return $ Mono ki'
    go_ki !env (ForAllKi kv inner) = do
      kibinder env kv $ \env' kv' -> do
        inner' <- go_ki env' inner
        return $ ForAllKi kv' inner'

    go_mono_ki !env (KiVarKi kv) = kivar env kv
    go_mono_ki !env ki@(KiConApp kc kis)
      | null kis
      = return ki
      | otherwise
      = mkKiConApp kc <$> go_mono_kis env kis
    go_mono_ki !env ki@(FunKi _ arg res) = do
      arg' <- go_mono_ki env arg
      res' <- go_mono_ki env res
      return ki { fk_arg = arg', fk_res = res' }

    
{- *********************************************************************
*                                                                      *
                      KiVarKi
*                                                                      *
********************************************************************* -}

getKiVar_maybe :: Kind -> Maybe KindVar
getKiVar_maybe (Mono (KiVarKi kv)) = Just kv
getKiVar_maybe _ = Nothing

getKiVarMono_maybe :: MonoKind -> Maybe KindVar
getKiVarMono_maybe (KiVarKi kv) = Just kv
getKiVarMono_maybe _ = Nothing

{- *********************************************************************
*                                                                      *
                      FunKi
*                                                                      *
********************************************************************* -}

chooseFunKiFlag :: MonoKind -> MonoKind -> FunKiFlag
chooseFunKiFlag arg_ki res_ki
  | KiConApp _ (_:_) <- res_ki
  = pprPanic "chooseFunKiFlag" (text "res_ki =" <+> ppr res_ki)
  | KiConApp _ (_:_) <- arg_ki
  = FKF_C_K
  | otherwise
  = FKF_K_K  

{-# INLINE splitFunKi_maybe #-}
splitFunKi_maybe :: Kind -> Maybe (FunKiFlag, MonoKind, MonoKind)
splitFunKi_maybe ki = case ki of
  (Mono (FunKi f arg res)) -> Just (f, arg, res)
  _ -> Nothing

mkKiConApp :: KiCon -> [MonoKind] -> MonoKind
mkKiConApp kicon kis = KiConApp kicon kis

{- *********************************************************************
*                                                                      *
                      ForAllKi
*                                                                      *
********************************************************************* -}

splitForAllKiVars :: Kind -> ([KindVar], MonoKind)
splitForAllKiVars ki = split ki []
  where
    split (ForAllKi kv ki) kvs = split ki (kv:kvs)
    split (Mono mki) kvs = (reverse kvs, mki)
