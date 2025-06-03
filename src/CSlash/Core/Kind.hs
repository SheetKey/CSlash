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
import Data.List (intersect)
import Data.Maybe (isJust)

{- **********************************************************************
*                                                                       *
                        Kind
*                                                                       *
********************************************************************** -}

data Kind v
  = ForAllKi {-# UNPACK #-} !KiVar Kind
  | Mono (MonoKind v)
  deriving Data.Data

data MonoKind v
  = KiVarKi v
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

instance Ord KiCon where
  compare k1 k2
    | _:_ <- (intersect [LTKi, LTEQKi, EQKi] [k1, k2]) = panic "Ord KiCon"
    | k1 == k2 = EQ
  compare UKd _ = LT
  compare _ UKd = GT
  compare AKd _ = LT
  compare _ AKd = GT
  compare k1 k2 = pprPanic "Ord KiCon unreachable" (ppr k1 <+> ppr k2)

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
  ppr UKd = uKindLit
  ppr AKd = aKindLit
  ppr LKd = lKindLit
  ppr LTKi = char '<'
  ppr LTEQKi = text "<="
  ppr EQKi = char '~'

instance Outputable v => Outputable (Kind v) where
  ppr = pprKind

instance Outputable v => Outputable (MonoKind v) where
  ppr = pprMonoKind

instance Eq v => Eq (MonoKind v) where
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

pprKind :: Outputable v => Kind v -> SDoc
pprKind = pprPrecKind topPrec

pprMonoKind :: Outputable v => MonoKind v -> SDoc
pprMonoKind = pprPrecMonoKind topPrec

pprParendMonoKind :: Outputable v => MonoKind v -> SDoc
pprParendMonoKind = pprPrecMonoKind appPrec

pprPrecKind :: Outputable v => PprPrec -> Kind v -> SDoc
pprPrecKind = pprPrecKindX emptyTidyEnv

pprPrecMonoKind :: Outputable v => PprPrec -> MonoKind v -> SDoc
pprPrecMonoKind = pprPrecMonoKindX emptyTidyEnv

pprPrecKindX :: Outputable v => MkTidyEnv v -> PprPrec -> Kind v -> SDoc
pprPrecKindX env prec ki
  = getPprStyle $ \sty ->
    getPprDebug $ \debug ->
    if debug
    then debug_ppr_ki prec ki
    else text "{pprKind not implemented}"--pprPrecIfaceKind prec (tidyToIfaceKindStyX env ty sty)

pprPrecMonoKindX :: Outputable v => MkTidyEnv v -> PprPrec -> MonoKind v -> SDoc
pprPrecMonoKindX env prec ki
  = getPprStyle $ \sty ->
    getPprDebug $ \debug ->
    if debug
    then debug_ppr_mono_ki prec ki
    else text "{pprKind not implemented}"--pprPrecIfaceKind prec (tidyToIfaceKindStyX env ty sty)

pprKiCo :: Outpurable v => KindCoercion v -> SDoc
pprKiCo = pprPrecKiCo topPrec

pprPrecKiCo :: Outputable v => PprPrec -> KindCoercion v -> SDoc
pprPrecKiCo = pprPrecKiCoX emptyTidyEnv

pprPrecKiCoX :: Outputable v => TidyEnv v -> PprPrec -> KindCoercion v -> SDoc
pprPrecKiCoX _ prec co = getPprStyle $ \sty ->
                       getPprDebug $ \debug ->
                       if debug
                       then debug_ppr_ki_co prec co
                       else panic "pprPrecKiCoX"

debugPprKind :: Outputable v => Kind v -> SDoc
debugPprKind ki = debug_ppr_ki topPrec ki

debugPprMonoKind :: Outputable v => MonoKind v -> SDoc
debugPprMonoKind ki = debug_ppr_mono_ki topPrec ki

debug_ppr_ki :: Outputable v => PprPrec -> Kind v -> SDoc
debug_ppr_ki prec (Mono ki) = debug_ppr_mono_ki prec ki
debug_ppr_ki prec ki
  | (bndrs, body) <- splitForAllKiVars ki
  , not (null bndrs)
  = maybeParen prec funPrec $ sep [ text "forall" <+> fsep (map (braces . ppr) bndrs) <> dot
                                  , ppr body ]
debug_ppr_ki _ _ = panic "debug_ppr_ki unreachable"

debug_ppr_mono_ki :: Outputable v => PprPrec -> MonoKind v -> SDoc
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
  = debug_ppr_mono_ki prec k1 <+> text "<=" <+> debug_ppr_mono_ki prec k2
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

debug_ppr_ki_co :: PprPrec -> KindCoercion -> SDoc
debug_ppr_ki_co _ (Refl ki) = angleBrackets (ppr ki)
debug_ppr_ki_co prec (FunCo _ _ co1 co2)
  = maybeParen prec funPrec
    $ sep (debug_ppr_ki_co funPrec co1 : ppr_fun_tail co2)
  where
    ppr_fun_tail (FunCo _ _ co1 co2)
      = (arrow <+> debug_ppr_ki_co funPrec co1)
        : ppr_fun_tail co2
    ppr_fun_tail other = [ arrow <+> ppr other ]
debug_ppr_ki_co prec (KiConAppCo kc [co1, co2]) = case kc of
  LTKi -> maybeParen prec appPrec (debug_ppr_ki_co prec co1) <+> char '<' <+>
          maybeParen prec appPrec (debug_ppr_ki_co prec co2)
  LTEQKi -> maybeParen prec appPrec (debug_ppr_ki_co prec co1) <+> text "<=" <+>
            maybeParen prec appPrec (debug_ppr_ki_co prec co2)
  EQKi -> maybeParen prec appPrec (debug_ppr_ki_co prec co1) <+> char '~' <+>
          maybeParen prec appPrec (debug_ppr_ki_co prec co2)
  other -> pprPanic "debug_ppr_ki_co kcappco" (ppr other)
debug_ppr_ki_co prec (SymCo co) = maybeParen prec appPrec $ sep [ text "Sym"
                                                                , nest 4 (ppr co) ]
debug_ppr_ki_co prec (TransCo co1 co2)
  = let ppr_trans (TransCo c1 c2) = semi <+> debug_ppr_ki_co topPrec c1 : ppr_trans c2
        ppr_trans c = [semi <+> debug_ppr_ki_co opPrec c]
  in maybeParen prec opPrec
     $ vcat (debug_ppr_ki_co topPrec co1 : ppr_trans co2)
debug_ppr_ki_co _ (HoleCo co) = ppr co
debug_ppr_ki_co _ _ = panic "debug_ppr_ki_co"

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

-- Simple Kind Constructors
class SKC kind where
  mkKiVarKi :: v -> kind v
  mkFunKi :: FunKiFlag -> kind v -> kind v -> kind v

instance SKC MonoKind where
  mkKiVarKi = KiVarKi
  mkFunKi f arg res = assertPpr (f == chooseFunKiFlag arg res)
                      (vcat [ text "f" <+> ppr f
                            , text "chooseF" <+> ppr (chooseFunKiFlag arg res)
                            , text "arg" <+> ppr arg
                            , text "res" <+> ppr res ])
                      $ FunKi { fk_f = f, fk_arg = arg, fk_res = res }

instance SKC Kind where
  mkKiVarKi = Mono . mkKiVarKi
  mkFunKi = Mono . mkFunKi

mkKiVarKi :: v -> Kind v
mkKiVarKi v = Mono $ KiVarKi v

mkKiVarMKi :: KiVar -> MonoKind
mkKiVarMKi v = assertPpr (isKiVar v) (ppr v) $ KiVarKi v


mkFunKi_nc :: FunKiFlag -> MonoKind -> MonoKind -> MonoKind
mkFunKi_nc f arg res = FunKi { fk_f = f, fk_arg = arg, fk_res = res }

mkVisFunKis :: [MonoKind] -> MonoKind -> MonoKind
mkVisFunKis args res = foldr (mkFunKi FKF_K_K) res args

mkInvisFunKis :: [MonoKind] -> MonoKind -> MonoKind
mkInvisFunKis args res = foldr (mkFunKi FKF_C_K) res args

mkInvisFunKis_nc :: [MonoKind] -> MonoKind -> MonoKind
mkInvisFunKis_nc args res = foldr (mkFunKi_nc FKF_C_K) res args

mkForAllKi :: KindVar -> Kind -> Kind
mkForAllKi v k = assertPpr (isKiVar v) (ppr v) $ ForAllKi v k

{- *********************************************************************
*                                                                      *
                Coercions
*                                                                      *
********************************************************************* -}

data KindCoercion v
  = Refl (MonoKind v)
  | KiConAppCo KiCon [KindCoercion v]
  | FunCo
    { fco_afl :: FunKiFlag
    , fco_afr :: FunKiFlag
    , fco_arg :: KindCoercion v
    , fco_res :: KindCoercion v }
  | KiCoVarCo KiCoVar
  | SymCo (KindCoercion v)
  | TransCo (KindCoercion v) (KindCoercion v)
  | HoleCo (KindCoercionHole v)
  deriving Data.Data

data KindCoercionHole v = CoercionHole
  { ch_co_var :: KiCoVar
  , ch_ref :: IORef (Maybe (KindCoercion v))
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

mkKiCoVarCo :: KiCoVar -> KindCoercion
mkKiCoVarCo cv = KiCoVarCo cv

mkKiEqPred :: MonoKind -> MonoKind -> PredKind
mkKiEqPred ki1 ki2 = mkKiConApp EQKi [ki1, ki2]

kicoercionLKind :: KindCoercion -> MonoKind
kicoercionLKind co = go co
  where
    go (Refl ki) = ki
    go (KiConAppCo kc cos) = mkKiConApp kc (map go cos)
    go (FunCo { fco_afl = af, fco_arg = arg, fco_res = res })
      = FunKi { fk_f = af, fk_arg = go arg, fk_res = go res }
    go (KiCoVarCo cv) = coVarLKind cv
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
    go (KiCoVarCo cv) = coVarRKind cv
    go (SymCo co) = kicoercionLKind co
    go (TransCo _ co2) = go co2
    go (HoleCo h) = coVarRKind (coHoleCoVar h)

instance Outputable KindCoercion where
  ppr = pprKiCo

instance Outputable KindCoercionHole where
  ppr (CoercionHole { ch_co_var = cv }) = braces (ppr cv)

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
  , kcf_covar :: env -> KiCoVar -> a
  , kcf_hole :: env -> KindCoercionHole -> a
  }

{-# INLINE foldMonoKiCo #-}
foldMonoKiCo
  :: Monoid a
  => MonoKiCoFolder env a
  -> env
  -> (MonoKind -> a, [MonoKind] -> a, KindCoercion -> a, [KindCoercion] -> a)
foldMonoKiCo (MKiCoFolder { kcf_kivar = kivar
                          , kcf_covar = covar
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
    go_co env (KiCoVarCo cv) = covar env cv

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

isKiVarKi :: MonoKind -> Bool
isKiVarKi ki = isJust (getKiVarMono_maybe ki)

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

isFunKi :: Kind -> Bool
isFunKi ki = case ki of
               (Mono (FunKi {})) -> True
               _ -> False

{-# INLINE splitFunKi_maybe #-}
splitFunKi_maybe :: Kind -> Maybe (FunKiFlag, MonoKind, MonoKind)
splitFunKi_maybe ki = case ki of
  (Mono (FunKi f arg res)) -> Just (f, arg, res)
  _ -> Nothing

{-# INLINE splitMonoFunKi_maybe #-}
splitMonoFunKi_maybe :: MonoKind -> Maybe  (FunKiFlag, MonoKind, MonoKind)
splitMonoFunKi_maybe ki = case ki of
  FunKi f arg res -> Just (f, arg, res)
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

splitPiKi_maybe :: Kind -> Maybe (Either (KindVar, Kind) (FunKiFlag, MonoKind, MonoKind))
splitPiKi_maybe ki = case ki of
  ForAllKi kv ki -> Just $ Left (kv, ki)
  Mono (FunKi { fk_f = af, fk_arg = arg, fk_res = res }) -> Just $ Right (af, arg, res)
  _ -> Nothing

isMonoFunKi :: MonoKind -> Bool
isMonoFunKi (FunKi {}) = True
isMonoFunKi _ = False

splitForAllKi_maybe :: Kind -> Maybe (KindVar, Kind)
splitForAllKi_maybe ki = case ki of
  ForAllKi kv ki -> Just (kv, ki)
  _ -> Nothing

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

isAtomicKi :: MonoKind -> Bool
isAtomicKi (KiVarKi {}) = True
isAtomicKi (KiConApp _ []) = True
isAtomicKi _ = False
