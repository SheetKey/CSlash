{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Core.Kind
  ( module CSlash.Core.Kind
  , KiVar
  ) where

import Prelude hiding ((<>))

import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set

import CSlash.Types.Basic
import CSlash.Types.Unique
import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.FV
import CSlash.Data.FastString
import CSlash.Data.Pair
import CSlash.Types.Unique.DFM

import Data.IORef
import qualified Data.Data as Data
import Data.List (intersect)
import Data.Maybe (isJust)
import Data.Void (Void)

{- **********************************************************************
*                                                                       *
                        Kind
*                                                                       *
********************************************************************** -}

data Kind kv
  = ForAllKi {-# UNPACK #-} !kv (Kind kv)
  | Mono (MonoKind kv)
  deriving Data.Data

data MonoKind kv
  = KiVarKi kv
  | KiConApp KiCon [MonoKind kv]
  | FunKi
    { fk_f :: FunKiFlag
    , fk_arg :: MonoKind kv
    , fk_res :: MonoKind kv
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

pprPrecKind :: Outputable kv => PprPrec -> Kind kv -> SDoc
pprPrecKind = pprPrecKindX @Void emptyTidyEnv

pprPrecMonoKind :: Outputable v => PprPrec -> MonoKind v -> SDoc
pprPrecMonoKind = pprPrecMonoKindX @Void emptyTidyEnv

pprPrecKindX
  :: forall tv kv. Outputable kv => MkTidyEnv tv kv -> PprPrec -> Kind kv -> SDoc
pprPrecKindX env prec ki
  = getPprStyle $ \sty ->
    getPprDebug $ \debug ->
    if debug
    then debug_ppr_ki prec ki
    else text "{pprKind not implemented}"--pprPrecIfaceKind prec (tidyToIfaceKindStyX env ty sty)

pprPrecMonoKindX
  :: forall tv kv. Outputable kv => MkTidyEnv tv kv -> PprPrec -> MonoKind kv -> SDoc
pprPrecMonoKindX env prec ki
  = getPprStyle $ \sty ->
    getPprDebug $ \debug ->
    if debug
    then debug_ppr_mono_ki prec ki
    else text "{pprKind not implemented}"--pprPrecIfaceKind prec (tidyToIfaceKindStyX env ty sty)

pprKiCo :: Outputable kv => KindCoercion kv -> SDoc
pprKiCo = pprPrecKiCo topPrec

pprPrecKiCo :: Outputable kv => PprPrec -> KindCoercion kv -> SDoc
pprPrecKiCo = pprPrecKiCoX emptyTidyEnv

pprPrecKiCoX
  :: Outputable kv
  => MkTidyEnv (KiCoVar kv) kv
  -> PprPrec
  -> KindCoercion kv
  -> SDoc
pprPrecKiCoX _ prec co = getPprStyle $ \sty ->
                       getPprDebug $ \debug ->
                       if debug
                       then debug_ppr_ki_co prec co
                       else panic "pprPrecKiCoX"

debugPprKind :: Outputable kv => Kind kv -> SDoc
debugPprKind ki = debug_ppr_ki topPrec ki

debugPprMonoKind :: Outputable kv => MonoKind kv -> SDoc
debugPprMonoKind ki = debug_ppr_mono_ki topPrec ki

debug_ppr_ki :: Outputable kv => PprPrec -> Kind kv -> SDoc
debug_ppr_ki prec (Mono ki) = debug_ppr_mono_ki prec ki
debug_ppr_ki prec ki
  | (bndrs, body) <- splitForAllKiVars ki
  , not (null bndrs)
  = maybeParen prec funPrec $ sep [ text "forall" <+> fsep (map (braces . ppr) bndrs) <> dot
                                  , ppr body ]
debug_ppr_ki _ _ = panic "debug_ppr_ki unreachable"

debug_ppr_mono_ki :: Outputable kv => PprPrec -> MonoKind kv -> SDoc
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

debug_ppr_ki_co :: Outputable kv => PprPrec -> KindCoercion kv -> SDoc
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

instance AsGenericKi Kind where
  asGenericKi (ForAllKi kv ki) = ForAllKi (toGenericKiVar kv) (asGenericKi ki)
  asGenericKi (Mono ki) = Mono (asGenericKi ki)

instance AsGenericKi MonoKind where
  asGenericKi (KiVarKi kv) = KiVarKi (toGenericKiVar kv)
  asGenericKi (KiConApp kc kis) = KiConApp kc (asGenericKi <$> kis)
  asGenericKi (FunKi f arg res) = FunKi f (asGenericKi arg) (asGenericKi res)

instance AsAnyKi Kind where
  asAnyKi (ForAllKi kv ki) = ForAllKi (toAnyKiVar kv) (asAnyKi ki)
  asAnyKi (Mono ki) = Mono (asAnyKi ki)

instance AsAnyKi MonoKind where
  asAnyKi (KiVarKi kv) = KiVarKi (toAnyKiVar kv)
  asAnyKi (KiConApp kc kis) = KiConApp kc (asAnyKi <$> kis)
  asAnyKi (FunKi f arg res) = FunKi f (asAnyKi arg) (asAnyKi res)

{- **********************************************************************
*                                                                       *
                        Kind FV instance
*                                                                       *
********************************************************************** -}

instance Uniquable kv => HasFVs (Kind kv) where
  type FVInScope (Kind kv) = MkVarSet kv
  type FVAcc (Kind kv) = ([kv], MkVarSet kv)
  type FVArg (Kind kv) = kv

  fvElemAcc kv (_, haveSet) = kv `elemVarSet` haveSet
  fvElemIS kv in_scope = kv `elemVarSet` in_scope

  fvExtendAcc kv (have, haveSet) = (kv:have, extendVarSet haveSet kv)
  fvExtendIS kv in_scope = extendVarSet in_scope kv

  fvEmptyAcc = ([], emptyVarSet)
  fvEmptyIS = emptyVarSet
  

{- **********************************************************************
*                                                                       *
            Simple constructors
*                                                                       *
********************************************************************** -}

-- Simple Kind Constructors
class SKC kind where
  mkKiVarKi :: v -> kind v

instance SKC MonoKind where
  mkKiVarKi = KiVarKi

instance SKC Kind where
  mkKiVarKi = Mono . mkKiVarKi

mkFunKi :: Outputable kv => FunKiFlag -> MonoKind kv -> MonoKind kv -> MonoKind kv
mkFunKi f arg res = assertPpr (f == chooseFunKiFlag arg res)
                    (vcat [ text "f" <+> ppr f
                          , text "chooseF" <+> ppr (chooseFunKiFlag arg res)
                          , text "arg" <+> ppr arg
                          , text "res" <+> ppr res ])
                    $ FunKi { fk_f = f, fk_arg = arg, fk_res = res }

mkFunKi_nc :: FunKiFlag -> MonoKind kv -> MonoKind kv -> MonoKind kv
mkFunKi_nc f arg res = FunKi { fk_f = f, fk_arg = arg, fk_res = res }

mkVisFunKis :: Outputable kv => [MonoKind kv] -> MonoKind kv -> MonoKind kv
mkVisFunKis args res = foldr (mkFunKi FKF_K_K) res args

mkInvisFunKis :: Outputable kv => [MonoKind kv] -> MonoKind kv -> MonoKind kv
mkInvisFunKis args res = foldr (mkFunKi FKF_C_K) res args

mkInvisFunKis_nc :: Outputable kv => [MonoKind kv] -> MonoKind kv -> MonoKind kv
mkInvisFunKis_nc args res = foldr (mkFunKi_nc FKF_C_K) res args

mkForAllKi :: kv -> Kind kv -> Kind kv
mkForAllKi = ForAllKi

{- *********************************************************************
*                                                                      *
                Coercions
*                                                                      *
********************************************************************* -}

data KindCoercion kv 
  = Refl (MonoKind kv)
  | KiConAppCo KiCon [KindCoercion kv]
  | FunCo
    { fco_afl :: FunKiFlag
    , fco_afr :: FunKiFlag
    , fco_arg :: KindCoercion kv
    , fco_res :: KindCoercion kv }
  | KiCoVarCo (KiCoVar kv)
  | SymCo (KindCoercion kv)
  | TransCo (KindCoercion kv) (KindCoercion kv)
  | HoleCo (KindCoercionHole kv)
  deriving Data.Data

data KindCoercionHole kv = CoercionHole
  { ch_co_var :: KiCoVar kv
  , ch_ref :: IORef (Maybe (KindCoercion kv))
  }

instance AsGenericKi KindCoercion
instance AsGenericKi KindCoercionHole

instance AsAnyKi KindCoercion where
  asAnyKi (Refl ki) = Refl $ asAnyKi ki
  asAnyKi (KiConAppCo kc cos) = KiConAppCo kc (asAnyKi <$> cos)
  asAnyKi (FunCo f1 f2 a r) = FunCo f1 f2 (asAnyKi a) (asAnyKi r)
  asAnyKi (KiCoVarCo cv) = KiCoVarCo $ asAnyKi cv
  asAnyKi (SymCo co) = SymCo $ asAnyKi co
  asAnyKi (TransCo co1 co2) = TransCo (asAnyKi co1) (asAnyKi co2)
  asAnyKi (HoleCo hole) = HoleCo $ asAnyKi hole

instance AsAnyKi KindCoercionHole where
  asAnyKi (CoercionHole v r) = panic "AsAnyKi KindCoeHole"

instance Data.Typeable kv => Data.Data (KindCoercionHole kv)

coHoleCoVar :: KindCoercionHole kv -> KiCoVar kv
coHoleCoVar = ch_co_var

isReflKiCo :: KindCoercion kv -> Bool
isReflKiCo (Refl{}) = True
isReflKiCo _ = False

isReflKiCo_maybe :: KindCoercion kv -> Maybe (MonoKind kv)
isReflKiCo_maybe (Refl ki) = Just ki
isReflKiCo_maybe _ = Nothing

mkReflKiCo :: MonoKind kv -> KindCoercion kv
mkReflKiCo ki = Refl ki

mkSymKiCo :: KindCoercion kv -> KindCoercion kv
mkSymKiCo co | isReflKiCo co = co
mkSymKiCo (SymCo co) = co
mkSymKiCo co = SymCo co

mkTransKiCo :: KindCoercion kv -> KindCoercion kv -> KindCoercion kv
mkTransKiCo co1 co2 | isReflKiCo co1 = co2
                    | isReflKiCo co2 = co1
mkTransKiCo co1 co2 = TransCo co1 co2

mkKiConAppCo :: HasDebugCallStack => KiCon -> [KindCoercion kv] -> KindCoercion kv
mkKiConAppCo kc cos
  | Just kis <- traverse isReflKiCo_maybe cos
  = mkReflKiCo (mkKiConApp kc kis)
  | otherwise = KiConAppCo kc cos

mkFunKiCo
  :: Outputable kv
  => FunKiFlag
  -> KindCoercion kv
  -> KindCoercion kv
  -> KindCoercion kv
mkFunKiCo af arg_co res_co = mkFunKiCo2 af af arg_co res_co

mkFunKiCo2
  :: Outputable kv
  => FunKiFlag
  -> FunKiFlag
  -> KindCoercion kv
  -> KindCoercion kv
  -> KindCoercion kv
mkFunKiCo2 afl afr arg_co res_co
  | Just ki1 <- isReflKiCo_maybe arg_co
  , Just ki2 <- isReflKiCo_maybe res_co
  = mkReflKiCo (mkFunKi afl ki1 ki2)
  | otherwise
  = FunCo { fco_afl = afl, fco_afr = afr
          , fco_arg = arg_co, fco_res = res_co }

mkKiCoVarCo :: KiCoVar kv -> KindCoercion kv
mkKiCoVarCo cv = KiCoVarCo cv

mkKiEqPred :: MonoKind kv -> MonoKind kv -> PredKind kv
mkKiEqPred ki1 ki2 = mkKiConApp EQKi [ki1, ki2]

kiCoercionKind :: IsVar kv => KindCoercion kv -> Pair (MonoKind kv)
kiCoercionKind co = Pair (kicoercionLKind co) (kicoercionRKind co)

kicoercionLKind :: IsVar kv => KindCoercion kv -> MonoKind kv
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

kicoercionRKind :: IsVar kv => KindCoercion kv -> MonoKind kv
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

instance Outputable kv => Outputable (KindCoercion kv) where
  ppr = pprKiCo

instance Outputable kv => Outputable (KindCoercionHole kv) where
  ppr (CoercionHole { ch_co_var = cv }) = braces (ppr cv)

instance Uniquable (KindCoercionHole kv) where
  getUnique (CoercionHole { ch_co_var = cv }) = getUnique cv

coVarLKind :: (HasDebugCallStack, IsVar kv) => KiCoVar kv -> MonoKind kv
coVarLKind cv | (ki1, _) <- coVarKinds cv = ki1

coVarRKind :: (HasDebugCallStack, IsVar kv) => KiCoVar kv -> MonoKind kv
coVarRKind cv | (_, ki2) <- coVarKinds cv = ki2

coVarKinds
  :: (HasDebugCallStack, IsVar kv)
  => KiCoVar kv
  -> (MonoKind kv, MonoKind kv)
coVarKinds cv
  | KiConApp EQKi [k1, k2] <- (varKind cv)
  = (k1, k2)
  | otherwise
  = pprPanic "coVarKinds" (ppr cv $$ ppr (varKind cv))

mkKiHoleCo :: KindCoercionHole kv -> KindCoercion kv
mkKiHoleCo h = HoleCo h

setCoHoleKind
  :: IsVar kv
  => KindCoercionHole kv
  -> MonoKind kv
  -> KindCoercionHole kv
setCoHoleKind h k = setCoHoleCoVar h (setVarKind (coHoleCoVar h) k)

setCoHoleCoVar :: KindCoercionHole kv -> KiCoVar kv -> KindCoercionHole kv
setCoHoleCoVar h cv = h { ch_co_var = cv }

{- **********************************************************************
*                                                                       *
            PredKind
*                                                                       *
********************************************************************** -}

type PredKind = MonoKind

isCoVarKind :: MonoKind kv -> Bool
isCoVarKind (KiConApp EQKi _) = True
isCoVarKind _ = False

isKiEvVarKind :: MonoKind kv -> Bool
isKiEvVarKind (KiConApp _ [_, _]) = True
isKiEvVarKind _ = False

{- *********************************************************************
*                                                                      *
                foldKiCo
*                                                                      *
********************************************************************* -}

data KiCoFolder kv env a = KiCoFolder
  { kcf_kibinder :: env -> kv -> env
  , kcf_mkcf :: MKiCoFolder kv env a
  }

data MKiCoFolder kv env a = MKiCoFolder
  { mkcf_kivar :: env -> kv -> a
  , mkcf_covar :: env -> KiCoVar kv -> a
  , mkcf_hole :: env -> KindCoercionHole kv -> a
  }

noKindView :: a -> Maybe a
noKindView _ = Nothing

{-# INLINE foldKind #-}
foldKind
  :: Monoid a
  => KiCoFolder kv env a
  -> env
  -> (Kind kv -> a, [Kind kv] -> a)
foldKind (KiCoFolder { kcf_kibinder = kibinder
                     , kcf_mkcf = mkcfolder
                     }) env
  = (go_ki env, go_kis env)
  where
    go_ki env (Mono ki) = go_mki ki
      where
        (go_mki, _, _, _) = foldMonoKiCo mkcfolder env
    go_ki env (ForAllKi kv inner)
      = let !env' = kibinder env kv
        in go_ki env' inner

    go_kis _ [] = mempty
    go_kis env (k:ks) = go_ki env k `mappend` go_kis env ks

{-# INLINE foldMonoKiCo #-}
foldMonoKiCo
  :: Monoid a
  => MKiCoFolder kv env a
  -> env
  -> (MonoKind kv -> a, [MonoKind kv] -> a, KindCoercion kv -> a, [KindCoercion kv] -> a)
foldMonoKiCo (MKiCoFolder { mkcf_kivar = kivar
                          , mkcf_covar = covar
                          , mkcf_hole = cohole }) env
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
                mapKiCo
*                                                                      *
********************************************************************* -}

data KiCoMapper kv kv' env m = KiCoMapper
  { kcm_kibinder :: forall r. env -> kv -> (env -> kv' -> m r) -> m r
  , kcm_mkcm :: MKiCoMapper kv kv' env m
  }

data MKiCoMapper kv kv' env m = MKiCoMapper
  { mkcm_kivar :: env -> kv -> m (MonoKind kv')
  , mkcm_covar :: env -> KiCoVar kv -> m (KindCoercion kv')
  , mkcm_hole :: env -> KindCoercionHole kv -> m (KindCoercion kv')
  }

{-# INLINE mapKind #-}
mapKind
  :: (Monad m, Outputable kv')
  => KiCoMapper kv kv' () m
  -> ( Kind kv -> m (Kind kv')
     , [Kind kv] -> m [Kind kv'] )
mapKind mapper = case mapKindX mapper of
  (go_ki, go_kis) -> (go_ki (), go_kis ())

{-# INLINE mapMKiCo #-}
mapMKiCo
  :: (Monad m, Outputable kv')
  => MKiCoMapper kv kv' () m
  -> ( MonoKind kv -> m (MonoKind kv')
     , [MonoKind kv] -> m [MonoKind kv']
     , KindCoercion kv -> m (KindCoercion kv')
     , [KindCoercion kv] -> m [KindCoercion kv'] )
mapMKiCo mapper = case mapMKiCoX mapper of
  (go_ki, go_kis, go_co, go_cos) -> (go_ki (), go_kis (), go_co (), go_cos ())

{-# INLINE mapKindX #-}
mapKindX
  :: (Monad m, Outputable kv')
  => KiCoMapper kv kv' env m
  -> ( env -> Kind kv -> m (Kind kv')
     , env -> [Kind kv] -> m [Kind kv'] )
mapKindX (KiCoMapper { kcm_kibinder = kibinder, kcm_mkcm = mkcmapper })
  = (go_ki, go_kis)
  where
    go_kis !_ [] = return []
    go_kis !env (ki:kis) = (:) <$> go_ki env ki <*> go_kis env kis

    (go_mki, _, _, _) = mapMKiCoX mkcmapper

    go_ki !env (Mono ki) = do
      ki' <- go_mki env ki
      return $ Mono ki'
    go_ki !env (ForAllKi kv inner) = do
      kibinder env kv $ \env' kv' -> do
        inner' <- go_ki env' inner
        return $ ForAllKi kv' inner'

{-# INLINE mapMKiCoX #-}
mapMKiCoX
  :: (Monad m, Outputable kv')
  => MKiCoMapper kv kv' env m
  -> ( env -> MonoKind kv -> m (MonoKind kv')
     , env -> [MonoKind kv] -> m [MonoKind kv']
     , env -> KindCoercion kv -> m (KindCoercion kv')
     , env -> [KindCoercion kv] -> m [KindCoercion kv'] )
mapMKiCoX (MKiCoMapper { mkcm_kivar = kivar, mkcm_covar = covar, mkcm_hole = cohole })
  = (go_mki, go_mkis, go_co, go_cos)
  where    
    go_mkis !_ [] = return []
    go_mkis !env (ki:kis) = (:) <$> go_mki env ki <*> go_mkis env kis

    go_mki !env (KiVarKi kv) = kivar env kv
    go_mki !env (KiConApp kc kis)
      | null kis
      = return (KiConApp kc [])
      | otherwise
      = mkKiConApp kc <$> go_mkis env kis
    go_mki !env ki@(FunKi _ arg res) = do
      arg' <- go_mki env arg
      res' <- go_mki env res
      return ki { fk_arg = arg', fk_res = res' }

    go_cos !_ [] = return []
    go_cos !env (co:cos) = (:) <$> go_co env co <*> go_cos env cos

    go_co !env (Refl ki) = Refl <$> go_mki env ki
    go_co !env (FunCo afl afr c1 c2) = mkFunKiCo2 afl afr <$> go_co env c1 <*> go_co env c2

    go_co !env (KiCoVarCo cv) = covar env cv
    go_co !env (HoleCo hole) = cohole env hole

    go_co !env (SymCo co) = mkSymKiCo <$> go_co env co
    go_co !env (TransCo c1 c2) = mkTransKiCo <$> go_co env c1 <*> go_co env c2

    go_co !env (KiConAppCo kc cos)
      | null cos
      = return $ KiConAppCo kc []
      | otherwise
      = mkKiConAppCo kc <$> go_cos env cos
    
{- *********************************************************************
*                                                                      *
                      KiVarKi
*                                                                      *
********************************************************************* -}

-- Simple Kind Getters
class SKG kind where
  getKiVar_maybe :: kind kv -> Maybe kv

instance SKG Kind where
  getKiVar_maybe (Mono (KiVarKi kv)) = Just kv
  getKiVar_maybe _ = Nothing

instance SKG MonoKind where
  getKiVar_maybe (KiVarKi kv) = Just kv
  getKiVar_maybe _ = Nothing

isKiVarKi :: SKG kind => kind kv -> Bool
isKiVarKi ki = isJust (getKiVar_maybe ki)

{- *********************************************************************
*                                                                      *
                      FunKi
*                                                                      *
********************************************************************* -}

chooseFunKiFlag :: Outputable kv => MonoKind kv -> MonoKind kv -> FunKiFlag
chooseFunKiFlag arg_ki res_ki
  | KiConApp _ (_:_) <- res_ki
  = pprPanic "chooseFunKiFlag" (text "res_ki =" <+> ppr res_ki)
  | KiConApp _ (_:_) <- arg_ki
  = FKF_C_K
  | otherwise
  = FKF_K_K  

isFunKi :: Kind kv -> Bool
isFunKi ki = case ki of
               (Mono (FunKi {})) -> True
               _ -> False

{-# INLINE splitFunKi_maybe #-}
splitFunKi_maybe :: Kind kv -> Maybe (FunKiFlag, MonoKind kv, MonoKind kv)
splitFunKi_maybe ki = case ki of
  (Mono (FunKi f arg res)) -> Just (f, arg, res)
  _ -> Nothing

{-# INLINE splitMonoFunKi_maybe #-}
splitMonoFunKi_maybe :: MonoKind kv -> Maybe  (FunKiFlag, MonoKind kv, MonoKind kv)
splitMonoFunKi_maybe ki = case ki of
  FunKi f arg res -> Just (f, arg, res)
  _ -> Nothing

mkKiConApp :: KiCon -> [MonoKind kv] -> MonoKind kv
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

splitPiKi_maybe :: Kind kv -> Maybe (Either (kv, Kind kv) (FunKiFlag, MonoKind kv, MonoKind kv))
splitPiKi_maybe ki = case ki of
  ForAllKi kv ki -> Just $ Left (kv, ki)
  Mono (FunKi { fk_f = af, fk_arg = arg, fk_res = res }) -> Just $ Right (af, arg, res)
  _ -> Nothing

isMonoFunKi :: MonoKind kv -> Bool
isMonoFunKi (FunKi {}) = True
isMonoFunKi _ = False

splitForAllKi_maybe :: Kind kv -> Maybe (kv, Kind kv)
splitForAllKi_maybe ki = case ki of
  ForAllKi kv ki -> Just (kv, ki)
  _ -> Nothing

splitForAllKiVars :: Kind kv -> ([kv], MonoKind kv)
splitForAllKiVars ki = split ki []
  where
    split (ForAllKi kv ki) kvs = split ki (kv:kvs)
    split (Mono mki) kvs = (reverse kvs, mki)

invisibleKiBndrCount :: MonoKind kv -> Int
invisibleKiBndrCount ki = length (fst (splitInvisFunKis ki))

splitFunKis :: MonoKind kv -> ([MonoKind kv], MonoKind kv)
splitFunKis ki = split ki []
  where
    split (FunKi { fk_arg = arg, fk_res = res }) bs = split res (arg:bs)
    split ki bs = (reverse bs, ki)

splitInvisFunKis :: MonoKind kv -> ([MonoKind kv], MonoKind kv)
splitInvisFunKis ki = split ki []
  where
    split (FunKi { fk_f = f, fk_arg = arg, fk_res = res }) bs
      | isInvisibleKiFunArg f = split res (arg:bs)
    split ki bs = (reverse bs, ki)

mkForAllKis :: [kv] -> Kind kv -> Kind kv
mkForAllKis kis ki = foldr ForAllKi ki kis

mkForAllKisMono :: [kv] -> MonoKind kv -> Kind kv
mkForAllKisMono kis mki = foldr ForAllKi (Mono mki) kis

isAtomicKi :: MonoKind kv -> Bool
isAtomicKi (KiVarKi {}) = True
isAtomicKi (KiConApp _ []) = True
isAtomicKi _ = False

