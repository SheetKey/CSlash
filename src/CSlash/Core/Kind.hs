{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Core.Kind where

import Prelude hiding ((<>))

import CSlash.Types.Var
import CSlash.Types.Var.Env

import CSlash.Types.Basic
import CSlash.Types.Unique
import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Data.FastString
import CSlash.Types.Unique.DFM

import Data.IORef
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
  | EQKi
  deriving (Show, Eq, Data.Data)

isEqualityKiCon :: KiCon -> Bool
isEqualityKiCon EQKi = True
isEqualityKiCon _ = False

type DKiConEnv a = UniqDFM KiCon a

isEmptyDKiConEnv :: DKiConEnv a -> Bool
isEmptyDKiConEnv = isNullUDFM

emptyDKiConEnv :: DKiConEnv a
emptyDKiConEnv = emptyUDFM

lookupDKiConEnv :: DKiConEnv a -> KiCon -> Maybe a
lookupDKiConEnv = lookupUDFM

adjustDKiConEnv :: (a -> a) -> DKiConEnv a -> KiCon -> DKiConEnv a
adjustDKiConEnv = adjustUDFM

alterDKiConEnv :: (Maybe a -> Maybe a) -> DKiConEnv a -> KiCon -> DKiConEnv a
alterDKiConEnv = alterUDFM

mapMaybeDKiConEnv :: (a -> Maybe b) -> DKiConEnv a -> DKiConEnv b
mapMaybeDKiConEnv = mapMaybeUDFM

foldDKiConEnv :: (a -> b -> b) -> b -> DKiConEnv a -> b
foldDKiConEnv = foldUDFM

instance Uniquable KiCon where
  getUnique kc = getUnique $ mkFastString $ show kc

instance Outputable KiCon where
  ppr _ = text "Outputable KiCon"

instance Outputable Kind where
  ppr = pprKind

instance Outputable MonoKind where
  ppr = pprMonoKind

instance Eq MonoKind where
  k1 == k2 = go k1 k2
    where
      go (KiConApp kc1 kis1) (KiConApp kc2 kis2)
        | kc1 == kc2
        = gos kis1 kis2
      go (KiVarKi v) (KiVarKi v') = v == v'
      go (FunKi v1 k1 k2) (FunKi v1' k1' k2') = (v1 == v1') && go k1 k1' && go k2 k2'
      go _ _ = False

      gos [] [] = True
      gos (k1:ks1) (k2:ks2) = go k1 k2 && gos ks1 ks2
      gos _ _ = False

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

debugPprMonoKind :: MonoKind -> SDoc
debugPprMonoKind ki = debug_ppr_mono_ki topPrec ki

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
  | EQKi <- kc
  , [k1, k2] <- args
  = debug_ppr_mono_ki prec k1 <+> text "~" <+> debug_ppr_mono_ki prec k2
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

mkFunKis :: [MonoKind] -> MonoKind -> MonoKind
mkFunKis args res = foldr (mkFunKi FKF_K_K) res args

mkForAllKi :: KindVar -> Kind -> Kind
mkForAllKi v k = assertPpr (isKiVar v) (ppr v) $ ForAllKi v k

{- *********************************************************************
*                                                                      *
                Coercions
*                                                                      *
********************************************************************* -}

data KindCoercion
  = Refl MonoKind
  | KiConAppCo KiCon [KindCoercion]
  | FunCo
    { fco_afl :: FunKiFlag
    , fco_afr :: FunKiFlag
    , fco_arg :: KindCoercion
    , fco_res :: KindCoercion }
  | SymCo KindCoercion
  | TransCo KindCoercion KindCoercion
  | HoleCo KindCoercionHole
  deriving Data.Data

data KindCoercionHole = CoercionHole
  { ch_co_var :: KiCoVar
  , ch_ref :: IORef (Maybe (KindCoercion))
  }

instance Data.Data KindCoercionHole

coHoleCoVar :: KindCoercionHole -> KiCoVar
coHoleCoVar = ch_co_var

isReflKiCo :: KindCoercion -> Bool
isReflKiCo (Refl{}) = True
isReflKiCo _ = False

isReflKiCo_maybe :: KindCoercion -> Maybe MonoKind
isReflKiCo_maybe (Refl ki) = Just ki
isReflKiCo_maybe _ = Nothing

mkReflKiCo :: MonoKind -> KindCoercion
mkReflKiCo ki = Refl ki

mkSymKiCo :: KindCoercion -> KindCoercion 
mkSymKiCo co | isReflKiCo co = co
mkSymKiCo (SymCo co) = co
mkSymKiCo co = SymCo co

mkTransKiCo :: KindCoercion -> KindCoercion -> KindCoercion
mkTransKiCo co1 co2 | isReflKiCo co1 = co2
                    | isReflKiCo co2 = co1
mkTransKiCo co1 co2 = TransCo co1 co2

mkKiConAppCo :: HasDebugCallStack => KiCon -> [KindCoercion] -> KindCoercion
mkKiConAppCo kc cos
  | Just kis <- traverse isReflKiCo_maybe cos
  = mkReflKiCo (mkKiConApp kc kis)
  | otherwise = KiConAppCo kc cos

mkFunKiCo :: FunKiFlag -> KindCoercion -> KindCoercion -> KindCoercion
mkFunKiCo af arg_co res_co = mkFunKiCo2 af af arg_co res_co

mkFunKiCo2 :: FunKiFlag -> FunKiFlag -> KindCoercion -> KindCoercion -> KindCoercion
mkFunKiCo2 afl afr arg_co res_co
  | Just ki1 <- isReflKiCo_maybe arg_co
  , Just ki2 <- isReflKiCo_maybe res_co
  = mkReflKiCo (mkFunKi afl ki1 ki2)
  | otherwise
  = FunCo { fco_afl = afl, fco_afr = afr
          , fco_arg = arg_co, fco_res = res_co }

mkKiEqPred :: MonoKind -> MonoKind -> PredKind
mkKiEqPred ki1 ki2 = mkKiConApp EQKi [ki1, ki2]

kicoercionLKind :: KindCoercion -> MonoKind
kicoercionLKind co = go co
  where
    go (Refl ki) = ki
    go (KiConAppCo kc cos) = mkKiConApp kc (map go cos)
    go (FunCo { fco_afl = af, fco_arg = arg, fco_res = res })
      = FunKi { fk_f = af, fk_arg = go arg, fk_res = go res }
    go (SymCo co) = kicoercionRKind co
    go (TransCo co1 _) = go co1
    go (HoleCo h) = coVarLKind (coHoleCoVar h)

kicoercionRKind :: KindCoercion -> MonoKind
kicoercionRKind co = go co
  where
    go (Refl ki) = ki
    go (KiConAppCo kc cos) = mkKiConApp kc (map go cos)
    go (FunCo { fco_afr = af, fco_arg = arg, fco_res = res })
      = FunKi { fk_f = af, fk_arg = go arg, fk_res = go res }
    go (SymCo co) = kicoercionLKind co
    go (TransCo _ co2) = go co2
    go (HoleCo h) = coVarRKind (coHoleCoVar h)

instance Outputable KindCoercion where
  ppr _ = text "Outputable KindCoercion"

instance Outputable KindCoercionHole where
  ppr _ = text "Outputable KindCoercionHole"

instance Uniquable KindCoercionHole where
  getUnique (CoercionHole { ch_co_var = cv }) = getUnique cv

coVarLKind :: HasDebugCallStack => KiCoVar -> MonoKind
coVarLKind cv | (ki1, _) <- coVarKinds cv = ki1

coVarRKind :: HasDebugCallStack => KiCoVar -> MonoKind
coVarRKind cv | (_, ki2) <- coVarKinds cv = ki2

coVarKinds :: HasDebugCallStack => KiCoVar -> (MonoKind, MonoKind)
coVarKinds cv
  | KiConApp EQKi [k1, k2] <- (varKind cv)
  = (k1, k2)
  | otherwise
  = pprPanic "coVarKinds" (ppr cv $$ ppr (varKind cv))

mkKiHoleCo :: KindCoercionHole -> KindCoercion
mkKiHoleCo h = HoleCo h

setCoHoleKind :: KindCoercionHole -> MonoKind -> KindCoercionHole
setCoHoleKind h k = setCoHoleCoVar h (setTyVarKind (coHoleCoVar h) k)

setCoHoleCoVar :: KindCoercionHole -> KiCoVar -> KindCoercionHole
setCoHoleCoVar h cv = h { ch_co_var = cv }

{- **********************************************************************
*                                                                       *
            PredKind
*                                                                       *
********************************************************************** -}

type PredKind = MonoKind

isCoVarKind :: MonoKind -> Bool
isCoVarKind (KiConApp EQKi _) = True
isCoVarKind _ = False

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

noKindView :: a -> Maybe a
noKindView _ = Nothing

data MonoKiCoFolder env a = MKiCoFolder
  { kcf_kivar :: env -> KindVar -> a
  , kcf_hole :: env -> KindCoercionHole -> a
  }

{-# INLINE foldMonoKiCo #-}
foldMonoKiCo
  :: Monoid a
  => MonoKiCoFolder env a
  -> env
  -> (MonoKind -> a, [MonoKind] -> a, KindCoercion -> a, [KindCoercion] -> a)
foldMonoKiCo (MKiCoFolder { kcf_kivar = kivar
                          , kcf_hole = cohole }) env
  = (go_ki env, go_kis env, go_co env, go_cos env)
  where
    go_ki env (KiVarKi kv) = kivar env kv
    go_ki env (FunKi _ arg res) = go_ki env arg `mappend` go_ki env res
    go_ki env (KiConApp _ kis) = go_kis env kis

    go_kis _ [] = mempty
    go_kis env (k:ks) = go_ki env k `mappend` go_kis env ks

    go_cos _ [] = mempty
    go_cos env (c:cs) = go_co env c `mappend` go_cos env cs

    go_co env (Refl ki) = go_ki env ki
    go_co env (KiConAppCo _ args) = go_cos env args
    go_co env (HoleCo hole) = cohole env hole
    go_co env (FunCo { fco_arg = c1, fco_res = c2 }) = go_co env c1 `mappend` go_co env c2

    go_co env (SymCo co) = go_co env co
    go_co env (TransCo c1 c2) = go_co env c1 `mappend` go_co env c2

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

isInvisibleKiFunArg :: FunKiFlag -> Bool
isInvisibleKiFunArg af = not (isVisibleKiFunArg af)

isVisibleKiFunArg :: FunKiFlag -> Bool
isVisibleKiFunArg FKF_K_K = True
isVisibleKiFunArg FKF_C_K = False

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

invisibleKiBndrCount :: MonoKind -> Int
invisibleKiBndrCount ki = length (fst (splitInvisFunKis ki))

splitFunKis :: MonoKind -> ([MonoKind], MonoKind)
splitFunKis ki = split ki []
  where
    split (FunKi { fk_arg = arg, fk_res = res }) bs = split res (arg:bs)
    split ki bs = (reverse bs, ki)

splitInvisFunKis :: MonoKind -> ([MonoKind], MonoKind)
splitInvisFunKis ki = split ki []
  where
    split (FunKi { fk_f = f, fk_arg = arg, fk_res = res }) bs
      | isInvisibleKiFunArg f = split res (arg:bs)
    split ki bs = (reverse bs, ki)

mkForAllKis :: [KindVar] -> Kind -> Kind
mkForAllKis kis ki = assertPpr (all isKiVar kis) (ppr kis) $ foldr ForAllKi ki kis

mkForAllKisMono :: [KindVar] -> MonoKind -> Kind
mkForAllKisMono kis mki = assertPpr (all isKiVar kis) (ppr kis) $ foldr ForAllKi (Mono mki) kis
