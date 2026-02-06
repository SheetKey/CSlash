{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
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

import {-# SOURCE #-} CSlash.Types.Var
import {-# SOURCE #-} CSlash.Core.Kind.Compare (eqMonoKind)

import CSlash.Cs.Pass

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
import CSlash.Data.Maybe
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

data Kind p
  = ForAllKi !(KiVar p) (Kind p)
  | Mono (MonoKind p)
  deriving Data.Data

data MonoKind p
  = KiVarKi (KiVar p)
  | BIKi BuiltInKi
  | KiPredApp KiPredCon (MonoKind p) (MonoKind p)
  | FunKi
    { fk_f :: FunKiFlag
    , fk_arg :: MonoKind p
    , fk_res :: MonoKind p
    }
  deriving Data.Data

data BuiltInKi
  = UKd
  | AKd
  | LKd
  deriving (Show, Eq, Ord, Data.Data)

data KiPredCon
  = LTKi
  | LTEQKi
  | EQKi
  deriving (Show, Eq, Data.Data)

-- Checks if a value with infered mult w1 is DEFINITELY allowed where a value of w2 is expected.
submult :: BuiltInKi -> MonoKind kv -> Bool
submult w1 (BIKi w2) = w1 >= w2
submult LKd _ = True
submult _ _ = False

-- type DKiConEnv a = UniqDFM KiCon a

-- isEmptyDKiConEnv :: DKiConEnv a -> Bool
-- isEmptyDKiConEnv = isNullUDFM

-- emptyDKiConEnv :: DKiConEnv a
-- emptyDKiConEnv = emptyUDFM

-- lookupDKiConEnv :: DKiConEnv a -> KiCon -> Maybe a
-- lookupDKiConEnv = lookupUDFM

-- adjustDKiConEnv :: (a -> a) -> DKiConEnv a -> KiCon -> DKiConEnv a
-- adjustDKiConEnv = adjustUDFM

-- alterDKiConEnv :: (Maybe a -> Maybe a) -> DKiConEnv a -> KiCon -> DKiConEnv a
-- alterDKiConEnv = alterUDFM

-- mapMaybeDKiConEnv :: (a -> Maybe b) -> DKiConEnv a -> DKiConEnv b
-- mapMaybeDKiConEnv = mapMaybeUDFM

-- foldDKiConEnv :: (a -> b -> b) -> b -> DKiConEnv a -> b
-- foldDKiConEnv = foldUDFM

instance Uniquable BuiltInKi where
  getUnique kc = getUnique $ mkFastString $ show kc

instance Outputable BuiltInKi where
  ppr UKd = uKindLit
  ppr AKd = aKindLit
  ppr LKd = lKindLit

instance Uniquable KiPredCon where
  getUnique pred = getUnique $ mkFastString $ show pred

instance Outputable KiPredCon where
  ppr LTKi = char '<'
  ppr LTEQKi = text "<="
  ppr EQKi = char '~'

instance Outputable (Kind p) where
  ppr = pprKind

instance Outputable (MonoKind p) where
  ppr = pprMonoKind

instance Eq (MonoKind p) where
  k1 == k2 = go k1 k2
    where
      go (BIKi k1) (BIKi k2) = k1 == k2
      go (KiPredApp p1 ka1 kb1) (KiPredApp p2 ka2 kb2)
        = p1 == p2 && ka1 == ka2 && kb1 == kb2
      go (KiVarKi v) (KiVarKi v') = v == v'
      go (FunKi v1 k1 k2) (FunKi v1' k1' k2') = (v1 == v1') && go k1 k1' && go k2 k2'
      go _ _ = False

      gos [] [] = True
      gos (k1:ks1) (k2:ks2) = go k1 k2 && gos ks1 ks2
      gos _ _ = False

pprKind :: Kind p -> SDoc
pprKind = pprPrecKind topPrec

pprMonoKind :: MonoKind p -> SDoc
pprMonoKind = pprPrecMonoKind topPrec

pprParendMonoKind :: MonoKind p -> SDoc
pprParendMonoKind = pprPrecMonoKind appPrec

pprPrecKind :: PprPrec -> Kind p -> SDoc
pprPrecKind = pprPrecKindX emptyTidyEnv

pprPrecMonoKind :: PprPrec -> MonoKind p -> SDoc
pprPrecMonoKind = pprPrecMonoKindX emptyTidyEnv

pprPrecKindX :: TidyEnv p -> PprPrec -> Kind p -> SDoc
pprPrecKindX env prec ki
  = getPprStyle $ \sty ->
    getPprDebug $ \debug ->
    if debug
    then debug_ppr_ki prec ki
    else text "{pprKind not implemented}"--pprPrecIfaceKind prec (tidyToIfaceKindStyX env ty sty)

pprPrecMonoKindX :: TidyEnv p -> PprPrec -> MonoKind p -> SDoc
pprPrecMonoKindX env prec ki
  = getPprStyle $ \sty ->
    getPprDebug $ \debug ->
    if debug
    then debug_ppr_mono_ki prec ki
    else text "{pprKind not implemented}"--pprPrecIfaceKind prec (tidyToIfaceKindStyX env ty sty)

pprKiCo :: KindCoercion p -> SDoc
pprKiCo = pprPrecKiCo topPrec

pprPrecKiCo :: PprPrec -> KindCoercion p -> SDoc
pprPrecKiCo = pprPrecKiCoX emptyTidyEnv

pprPrecKiCoX
  :: TidyEnv p
  -> PprPrec
  -> KindCoercion p
  -> SDoc
pprPrecKiCoX _ prec co = getPprStyle $ \sty ->
                       getPprDebug $ \debug ->
                       if debug
                       then debug_ppr_ki_co prec co
                       else panic "pprPrecKiCoX"

debugPprKind :: Kind p -> SDoc
debugPprKind ki = debug_ppr_ki topPrec ki

debugPprMonoKind :: MonoKind p -> SDoc
debugPprMonoKind ki = debug_ppr_mono_ki topPrec ki

debug_ppr_ki :: PprPrec -> Kind p -> SDoc
debug_ppr_ki prec (Mono ki) = debug_ppr_mono_ki prec ki
debug_ppr_ki prec ki
  | (bndrs, body) <- splitForAllKiVars ki
  , not (null bndrs)
  = maybeParen prec funPrec $ sep [ text "forall" <+> fsep (map (braces . ppr) bndrs) <> dot
                                  , ppr body ]
debug_ppr_ki _ _ = panic "debug_ppr_ki unreachable"

debug_ppr_mono_ki :: PprPrec -> MonoKind p -> SDoc
debug_ppr_mono_ki _ (KiVarKi kv) = ppr kv
debug_ppr_mono_ki _ (BIKi ki) = ppr ki
debug_ppr_mono_ki prec ki@(KiPredApp pred k1 k2)
  = maybeParen prec appPrec
    $ debug_ppr_mono_ki appPrec k1 <+> ppr pred <+> debug_ppr_mono_ki appPrec k2
debug_ppr_mono_ki prec (FunKi { fk_f = f, fk_arg = arg, fk_res = res })
  = maybeParen prec funPrec
    $ sep [ debug_ppr_mono_ki funPrec arg, fun_arrow <+> debug_ppr_mono_ki prec res]
  where
    fun_arrow = case f of
                  FKF_C_K -> darrow
                  FKF_K_K -> arrow

debug_ppr_ki_co :: PprPrec -> KindCoercion p -> SDoc
debug_ppr_ki_co _ (Refl ki) = angleBrackets (ppr ki)
debug_ppr_ki_co _ BI_U_A = angleBrackets (text "UKd < AKd")
debug_ppr_ki_co _ BI_A_L = angleBrackets (text "AKd < LKd")
debug_ppr_ki_co _ (BI_U_LTEQ ki) = angleBrackets (text "UKd < " <> ppr ki)
debug_ppr_ki_co _ (BI_LTEQ_L ki) = angleBrackets (ppr ki <> text " < LKd")
debug_ppr_ki_co _ (LiftEq ki) = angleBrackets (text "LiftEq" <+> ppr ki)
debug_ppr_ki_co _ (LiftLT ki) = angleBrackets (text "LiftLT" <+> ppr ki)
debug_ppr_ki_co prec (FunCo _ _ co1 co2)
  = maybeParen prec funPrec
    $ sep (debug_ppr_ki_co funPrec co1 : ppr_fun_tail co2)
  where
    ppr_fun_tail (FunCo _ _ co1 co2)
      = (arrow <+> debug_ppr_ki_co funPrec co1)
        : ppr_fun_tail co2
    ppr_fun_tail other = [ arrow <+> ppr other ]
debug_ppr_ki_co prec (SymCo co) = maybeParen prec appPrec $ sep [ text "Sym"
                                                                , nest 4 (ppr co) ]
debug_ppr_ki_co prec (TransCo co1 co2)
  = let ppr_trans (TransCo c1 c2) = semi <+> debug_ppr_ki_co topPrec c1 : ppr_trans c2
        ppr_trans c = [semi <+> debug_ppr_ki_co opPrec c]
  in maybeParen prec opPrec
     $ vcat (debug_ppr_ki_co topPrec co1 : ppr_trans co2)
debug_ppr_ki_co _ (HoleCo co) = ppr co
debug_ppr_ki_co _ (KiCoVarCo cv) = ppr cv
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
                        Kind FV instance
*                                                                       *
********************************************************************** -}

instance HasFVs (Kind p) where
  type FVInScope (Kind p) = KiVarSet p
  type FVAcc (Kind p) = ([KiVar p], KiVarSet p)
  type FVArg (Kind p) = KiVar p

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
  mkKiVarKi :: KiVar p -> kind p
  mkKiVarKis :: [KiVar p] -> [kind p]
  mkKiVarKis = map mkKiVarKi

instance SKC MonoKind where
  mkKiVarKi = KiVarKi

instance SKC Kind where
  mkKiVarKi = Mono . mkKiVarKi

mkFunKi :: FunKiFlag -> MonoKind p -> MonoKind p -> MonoKind p
mkFunKi f arg res = assertPpr (f == chooseFunKiFlag arg res)
                    (vcat [ text "f" <+> ppr f
                          , text "chooseF" <+> ppr (chooseFunKiFlag arg res)
                          , text "arg" <+> ppr arg
                          , text "res" <+> ppr res ])
                    $ FunKi { fk_f = f, fk_arg = arg, fk_res = res }

mkFunKi_nc :: FunKiFlag -> MonoKind kv -> MonoKind kv -> MonoKind kv
mkFunKi_nc f arg res = FunKi { fk_f = f, fk_arg = arg, fk_res = res }

mkVisFunKis :: [MonoKind p] -> MonoKind p -> MonoKind p
mkVisFunKis args res = foldr (mkFunKi FKF_K_K) res args

mkInvisFunKis :: [MonoKind p] -> MonoKind p -> MonoKind p
mkInvisFunKis args res = foldr (mkFunKi FKF_C_K) res args

mkInvisFunKis_nc :: [MonoKind p] -> MonoKind p -> MonoKind p
mkInvisFunKis_nc args res = foldr (mkFunKi_nc FKF_C_K) res args

mkForAllKi :: KiVar p -> Kind p -> Kind p
mkForAllKi = ForAllKi

mkPiKi :: (HasDebugCallStack) => PiKiBinder p -> Kind p -> Kind p
mkPiKi (Anon ki1 af) (Mono ki2) = Mono $ mkFunKi af ki1 ki2
mkPiKi (Named bndr) ki = mkForAllKi bndr ki
mkPiKi other_b other_k = pprPanic "mkPiKi" (panic "ppr other_b $$ ppr other_k")

mkPiKis :: (HasDebugCallStack) => [PiKiBinder p] -> Kind p -> Kind p
mkPiKis kbs ki = foldr mkPiKi ki kbs

{- *********************************************************************
*                                                                      *
                Coercions
*                                                                      *
********************************************************************* -}

data KindCoercion p where
  Refl :: (MonoKind p) -- refl : kv = kv
    -> KindCoercion p
  BI_U_A             -- builtin : u < a
    :: KindCoercion p
  BI_A_L             -- builtin : a < l
    :: KindCoercion p
  BI_U_LTEQ :: (MonoKind p)
    -> KindCoercion p
  BI_LTEQ_L :: (MonoKind p)
    -> KindCoercion p
  LiftEq :: (KindCoercion p) -- LiftEq : (kv = kv) -> (kv <= kv)
    -> KindCoercion p
  LiftLT :: (KindCoercion p) -- LiftLT : (kv1 < kv2) -> (kv1 <= kv2)
    -> KindCoercion p
  FunCo ::
    { fco_afl :: FunKiFlag
    , fco_afr :: FunKiFlag
    , fco_arg :: KindCoercion p
    , fco_res :: KindCoercion p }
    -> KindCoercion p
  KiCoVarCo :: (KiCoVar p) -> KindCoercion p
  SymCo :: (KindCoercion p) -> KindCoercion p
  TransCo :: (KindCoercion p) -> (KindCoercion p) -> KindCoercion p
  SelCo :: CoSel -> (KindCoercion p) -> KindCoercion p
  HoleCo :: KindCoercionHole -> KindCoercion Tc

instance Data.Typeable p => Data.Data (KindCoercion p)

data KindCoercionHole = KindCoercionHole
  { kch_co_var :: TcKiCoVar
  , kch_ref :: IORef (Maybe (KindCoercion Tc))
  }

data CoSel
  = SelFun FunSel
  deriving Data.Data

data FunSel = SelArg | SelRes
  deriving Data.Data

instance Outputable CoSel where
  ppr (SelFun fs) = text "Fun" <> parens (ppr fs)

instance Outputable FunSel where
  ppr SelArg = text "arg"
  ppr SelRes = text "res"

instance Data.Data KindCoercionHole

coHoleCoVar :: KindCoercionHole -> TcKiCoVar 
coHoleCoVar = kch_co_var

isReflKiCo :: KindCoercion p -> Bool
isReflKiCo (Refl{}) = True
isReflKiCo _ = False

isReflKiCo_maybe :: KindCoercion p -> Maybe (MonoKind p)
isReflKiCo_maybe (Refl ki) = Just ki
isReflKiCo_maybe _ = Nothing

mkSelCo
  :: HasDebugCallStack => CoSel -> KindCoercion p -> KindCoercion p
mkSelCo n co = mkSelCo_maybe n co `orElse` SelCo n co

mkSelCo_maybe
  :: HasDebugCallStack => CoSel -> KindCoercion p -> Maybe (KindCoercion p)
mkSelCo_maybe cs co
  = assertPpr (good_call cs) bad_call_msg
    $ panic "go cs co"
  where
    go (SelFun SelArg) (FunCo _ _ arg _) = Just arg
    go (SelFun SelRes) (FunCo _ _ _ res) = Just res
    go cs (SymCo co) = do
      co' <- go cs co
      return $ mkSymKiCo co'
    go cs co
      | Just ki <- isReflKiCo_maybe co
      = Just (mkReflKiCo (selectFromKind cs ki))

      | (EQKi, Pair ki1 ki2) <- kiCoercionParts co
      , let ski1 = selectFromKind cs ki1
            ski2 = selectFromKind cs ki2
      , ski1 `eqMonoKind` ski2
      = Just (mkReflKiCo ski1)
      | otherwise = Nothing

    (pred, Pair ki1 ki2) = kiCoercionParts co
    bad_call_msg = vcat [ text "KindCoercion =" <+> ppr co
                        , text "LHS ki =" <+> ppr ki1
                        , text "KiPred =" <+> ppr pred
                        , text "RHS ki =" <+> ppr ki2
                        , text "cs =" <+> ppr cs ]

    good_call SelFun{} = isMonoFunKi ki1 && isMonoFunKi ki2 && pred == EQKi      

selectFromKind :: (HasDebugCallStack) => CoSel -> MonoKind p -> MonoKind p
selectFromKind (SelFun SelArg) ki
  | Just (_, arg, _) <- splitMonoFunKi_maybe ki
  = arg
selectFromKind  (SelFun SelRes) ki
  | Just (_, _, res) <- splitMonoFunKi_maybe ki
  = res
selectFromKind cs ki = pprPanic "selectFromKind" (ppr cs $$ ppr ki)

mkReflKiCo :: MonoKind kv -> KindCoercion kv
mkReflKiCo ki = Refl ki

mkSymKiCo :: KindCoercion kv -> KindCoercion kv
mkSymKiCo co | isReflKiCo co = co
mkSymKiCo (SymCo co) = co
mkSymKiCo co = SymCo co

mkSymMKiCo :: Maybe (KindCoercion kv) -> Maybe (KindCoercion kv)
mkSymMKiCo = fmap mkSymKiCo

mkTransKiCo :: KindCoercion kv -> KindCoercion kv -> KindCoercion kv
mkTransKiCo co1 co2 | isReflKiCo co1 = co2
                    | isReflKiCo co2 = co1
mkTransKiCo co1 co2 = TransCo co1 co2

mkTransMKiCoR :: KindCoercion kv -> Maybe (KindCoercion kv) -> Maybe (KindCoercion kv)
mkTransMKiCoR co1 Nothing = if isReflKiCo co1 then Nothing else Just co1
mkTransMKiCoR co1 (Just co2) = Just $ mkTransKiCo co1 co2

mkFunKiCo
  :: FunKiFlag
  -> KindCoercion p
  -> KindCoercion p
  -> KindCoercion p
mkFunKiCo af arg_co res_co = mkFunKiCo2 af af arg_co res_co

mkFunKiCo2
  :: FunKiFlag
  -> FunKiFlag
  -> KindCoercion p
  -> KindCoercion p
  -> KindCoercion p
mkFunKiCo2 afl afr arg_co res_co
  | Just ki1 <- isReflKiCo_maybe arg_co
  , Just ki2 <- isReflKiCo_maybe res_co
  = mkReflKiCo (mkFunKi afl ki1 ki2)
  | otherwise
  = FunCo { fco_afl = afl, fco_afr = afr
          , fco_arg = arg_co, fco_res = res_co }

mkKiCoVarCo :: KiCoVar p -> KindCoercion p
mkKiCoVarCo cv = KiCoVarCo cv

mkKiCoVarCos :: [KiCoVar p] -> [KindCoercion p]
mkKiCoVarCos = map KiCoVarCo

mkKiCoPred :: KiPredCon -> MonoKind kv -> MonoKind kv -> PredKind kv
mkKiCoPred p ki1 ki2 = mkKiPredApp p ki1 ki2

kiCoercionParts :: KindCoercion p -> (KiPredCon, Pair (MonoKind p))
kiCoercionParts co = (kiCoercionPred co, Pair (kicoercionLKind co) (kicoercionRKind co))

kiCoercionKind :: KindCoercion p -> MonoKind p
kiCoercionKind co = case kiCoercionParts co of
  (pred, Pair k1 k2) -> mkKiPredApp pred k1 k2

kiCoercionPred :: KindCoercion p -> KiPredCon
kiCoercionPred co = go co
  where
    go (Refl _) = EQKi
    go BI_U_A = LTKi
    go BI_A_L = LTKi
    go (BI_U_LTEQ _) = LTEQKi
    go (BI_LTEQ_L _) = LTEQKi
    go (LiftEq co) = assertPpr (go co == EQKi) (vcat [text "kiCoercionPred: LiftEq co"
                                                     , text "but co does not have pred 'EQKi'" ])
                     LTEQKi
    go (LiftLT co) = assertPpr (go co == LTKi) (vcat [text "kiCoercionPred: LiftLT co"
                                                     , text "but co does not have pred 'LTKi'" ])
                     LTEQKi
    go (FunCo{}) = panic "kiCoercionPred/FunCo"
    go (KiCoVarCo cv) = kiCoVarKiPred cv
    go (SymCo co) = case go co of
                      EQKi -> EQKi
                      _ -> panic "kiCoercionPred/SymCo"
    go (TransCo co1 co2) = case (go co1, go co2) of
                             (EQKi, kc) -> kc
                             (kc, EQKi) -> kc
                             (LTEQKi, kc) -> kc
                             (kc, LTEQKi) -> kc
                             (LTKi, LTKi) -> LTKi
                             (_, _) -> panic "kiCoercionPred/TransCo"
    go (HoleCo h) = kiCoVarKiPred (coHoleCoVar h)
    go (SelCo{}) = EQKi

kicoercionLKind :: KindCoercion p -> MonoKind p
kicoercionLKind co = go co
  where
    go (Refl ki) = ki
    go BI_U_A = BIKi UKd
    go BI_A_L = BIKi AKd
    go (BI_U_LTEQ _) = BIKi UKd
    go (BI_LTEQ_L ki) = ki
    go (LiftEq co) = kicoercionLKind co
    go (LiftLT co) = kicoercionLKind co
    go (FunCo { fco_afl = af, fco_arg = arg, fco_res = res })
      = FunKi { fk_f = af, fk_arg = go arg, fk_res = go res }
    go (KiCoVarCo cv) = coVarLKind cv
    go (SymCo co) = kicoercionRKind co
    go (TransCo co1 _) = go co1
    go (SelCo d co) = selectFromKind d (go co)
    go (HoleCo h) = coVarLKind (coHoleCoVar h)

kicoercionRKind :: KindCoercion p -> MonoKind p
kicoercionRKind co = go co
  where
    go (Refl ki) = ki
    go BI_U_A = BIKi AKd
    go BI_A_L = BIKi LKd
    go (BI_U_LTEQ ki) = ki
    go (BI_LTEQ_L _) = BIKi LKd
    go (LiftEq co) = kicoercionRKind co
    go (LiftLT co) = kicoercionRKind co
    go (FunCo { fco_afr = af, fco_arg = arg, fco_res = res })
      = FunKi { fk_f = af, fk_arg = go arg, fk_res = go res }
    go (KiCoVarCo cv) = coVarRKind cv
    go (SymCo co) = kicoercionLKind co
    go (TransCo _ co2) = go co2
    go (SelCo d co) = selectFromKind d (go co)
    go (HoleCo h) = coVarRKind (coHoleCoVar h)

instance Outputable (KindCoercion p) where
  ppr = pprKiCo

instance  Outputable KindCoercionHole where
  ppr (KindCoercionHole { kch_co_var = cv }) = braces (ppr cv)

instance Uniquable KindCoercionHole where
  getUnique (KindCoercionHole { kch_co_var = cv }) = getUnique cv

kiCoVarKiPred :: (HasDebugCallStack, Outputable cv, VarHasKind cv p) => cv -> KiPredCon
kiCoVarKiPred cv | (kc, _, _) <- coVarKinds cv = kc

coVarLKind :: (HasDebugCallStack, Outputable cv, VarHasKind cv p) => cv -> MonoKind p
coVarLKind cv | (_, ki1, _) <- coVarKinds cv = ki1

coVarRKind :: (HasDebugCallStack, Outputable cv, VarHasKind cv p) => cv -> MonoKind p
coVarRKind cv | (_, _, ki2) <- coVarKinds cv = ki2

coVarKinds
  :: (HasDebugCallStack, Outputable cv, VarHasKind cv p)
  => cv
  -> (KiPredCon, MonoKind p, MonoKind p)
coVarKinds cv
  | KiPredApp kc k1 k2 <- (varKind cv)
  = (kc, k1, k2)
  | otherwise
  = pprPanic "coVarKinds" (ppr cv $$ ppr (varKind cv))

mkKiHoleCo :: KindCoercionHole -> KindCoercion Tc
mkKiHoleCo h = HoleCo h

setCoHoleKind
  :: KindCoercionHole
  -> MonoKind Tc
  -> KindCoercionHole
setCoHoleKind h k = setCoHoleCoVar h (setVarKind (coHoleCoVar h) k)

setCoHoleCoVar :: KindCoercionHole -> TcKiCoVar -> KindCoercionHole
setCoHoleCoVar h cv = h { kch_co_var = cv }

{- **********************************************************************
*                                                                       *
            PredKind
*                                                                       *
********************************************************************** -}

type PredKind = MonoKind

isKiCoVarKind :: MonoKind kv -> Bool
isKiCoVarKind (KiPredApp {}) = True
isKiCoVarKind _ = False

{- *********************************************************************
*                                                                      *
                foldKiCo
*                                                                      *
********************************************************************* -}

data KiCoFolder p env a = KiCoFolder
  { kcf_kibinder :: env -> KiVar p -> env
  , kcf_mkcf :: MKiCoFolder p env a
  }

data MKiCoFolder p env a = MKiCoFolder
  { mkcf_kivar :: env -> KiVar p -> a
  , mkcf_covar :: env -> KiCoVar p -> a
  , mkcf_hole :: env -> KindCoercionHole -> a
  }

noKindView :: a -> Maybe a
noKindView _ = Nothing

{-# INLINE foldKind #-}
foldKind
  :: Monoid a
  => KiCoFolder p env a
  -> env
  -> (Kind p -> a, [Kind p] -> a)
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
  => MKiCoFolder p env a
  -> env
  -> (MonoKind p -> a, [MonoKind p] -> a, KindCoercion p -> a, [KindCoercion p] -> a)
foldMonoKiCo (MKiCoFolder { mkcf_kivar = kivar
                          , mkcf_covar = covar
                          , mkcf_hole = cohole }) env
  = (go_ki env, go_kis env, go_co env, go_cos env)
  where
    go_ki env (KiVarKi kv) = kivar env kv
    go_ki env (BIKi _) = mempty
    go_ki env (FunKi _ arg res) = go_ki env arg `mappend` go_ki env res
    go_ki env (KiPredApp _ k1 k2) = go_ki env k1 `mappend` go_ki env k2

    go_kis _ [] = mempty
    go_kis env (k:ks) = go_ki env k `mappend` go_kis env ks

    go_cos _ [] = mempty
    go_cos env (c:cs) = go_co env c `mappend` go_cos env cs

    go_co env (Refl ki) = go_ki env ki
    go_co env BI_U_A = mempty
    go_co env BI_A_L = mempty
    go_co env (BI_U_LTEQ ki) = go_ki env ki
    go_co env (BI_LTEQ_L ki) = go_ki env ki
    go_co env (LiftEq co) = go_co env co
    go_co env (LiftLT co) = go_co env co
    go_co env (HoleCo hole) = cohole env hole
    go_co env (FunCo { fco_arg = c1, fco_res = c2 }) = go_co env c1 `mappend` go_co env c2
    go_co env (SelCo _ co) = go_co env co
    go_co env (KiCoVarCo cv) = covar env cv

    go_co env (SymCo co) = go_co env co
    go_co env (TransCo c1 c2) = go_co env c1 `mappend` go_co env c2

{- *********************************************************************
*                                                                      *
                mapKiCo
*                                                                      *
********************************************************************* -}

data KiCoMapper p p' env m = KiCoMapper
  { kcm_kibinder :: forall r. env -> KiVar p -> (env -> KiVar p' -> m r) -> m r
  , kcm_mkcm :: MKiCoMapper p p' env m
  }

data MKiCoMapper p p' env m = MKiCoMapper
  { mkcm_kivar :: env -> KiVar p -> m (MonoKind p')
  , mkcm_covar :: env -> KiCoVar p -> m (KindCoercion p')
  , mkcm_hole :: env -> KindCoercionHole -> m (KindCoercion p')
  }

{-# INLINE mapKind #-}
mapKind
  :: Monad m
  => KiCoMapper p p' () m
  -> ( Kind p -> m (Kind p')
     , [Kind p] -> m [Kind p'] )
mapKind mapper = case mapKindX mapper of
  (go_ki, go_kis) -> (go_ki (), go_kis ())

{-# INLINE mapMKiCo #-}
mapMKiCo
  :: Monad m
  => MKiCoMapper p p' () m
  -> ( MonoKind p -> m (MonoKind p')
     , [MonoKind p] -> m [MonoKind p']
     , KindCoercion p -> m (KindCoercion p')
     , [KindCoercion p] -> m [KindCoercion p'] )
mapMKiCo mapper = case mapMKiCoX mapper of
  (go_ki, go_kis, go_co, go_cos) -> (go_ki (), go_kis (), go_co (), go_cos ())

{-# INLINE mapKindX #-}
mapKindX
  :: Monad m
  => KiCoMapper p p' env m
  -> ( env -> Kind p -> m (Kind p')
     , env -> [Kind p] -> m [Kind p'] )
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
  :: Monad m
  => MKiCoMapper p p' env m
  -> ( env -> MonoKind p -> m (MonoKind p')
     , env -> [MonoKind p] -> m [MonoKind p']
     , env -> KindCoercion p -> m (KindCoercion p')
     , env -> [KindCoercion p] -> m [KindCoercion p'] )
mapMKiCoX (MKiCoMapper { mkcm_kivar = kivar, mkcm_covar = covar, mkcm_hole = cohole })
  = (go_mki, go_mkis, go_co, go_cos)
  where    
    go_mkis !_ [] = return []
    go_mkis !env (ki:kis) = (:) <$> go_mki env ki <*> go_mkis env kis

    go_mki !env (KiVarKi kv) = kivar env kv
    go_mki !env (BIKi k) = return $ BIKi k
    go_mki !env (KiPredApp pred ki1 ki2)
      = mkKiPredApp pred <$> go_mki env ki1 <*> go_mki env ki2
    go_mki !env ki@(FunKi _ arg res) = do
      arg' <- go_mki env arg
      res' <- go_mki env res
      return ki { fk_arg = arg', fk_res = res' }

    go_cos !_ [] = return []
    go_cos !env (co:cos) = (:) <$> go_co env co <*> go_cos env cos

    go_co !env (Refl ki) = Refl <$> go_mki env ki
    go_co !env BI_U_A = return BI_U_A
    go_co !env BI_A_L = return BI_A_L
    go_co !env (BI_U_LTEQ ki) = BI_U_LTEQ <$> go_mki env ki
    go_co !env (BI_LTEQ_L ki) = BI_LTEQ_L <$> go_mki env ki
    go_co !env (LiftEq co) = LiftEq <$> go_co env co
    go_co !env (LiftLT co) = LiftLT <$> go_co env co

    go_co !env (FunCo afl afr c1 c2) = mkFunKiCo2 afl afr <$> go_co env c1 <*> go_co env c2

    go_co !env (KiCoVarCo cv) = covar env cv
    go_co !env (HoleCo hole) = cohole env hole

    go_co !env (SymCo co) = mkSymKiCo <$> go_co env co
    go_co !env (TransCo c1 c2) = mkTransKiCo <$> go_co env c1 <*> go_co env c2
    go_co !env (SelCo i co) = mkSelCo i <$> go_co env co

closedKind :: Kind p -> Maybe (Kind p')
closedKind = case mapKind kcvClosedMapper of
               (f, _) -> f

closedMonoKind :: MonoKind p -> Maybe (MonoKind p')
closedMonoKind = case mapMKiCo mkcvClosedMapper of
                   (f, _, _, _) -> f

closedMonoKinds :: [MonoKind p] -> Maybe [MonoKind p']
closedMonoKinds = case mapMKiCo mkcvClosedMapper of
                    (_, f, _, _) -> f

closedKiCo :: KindCoercion p -> Maybe (KindCoercion p')
closedKiCo = case mapMKiCo mkcvClosedMapper of
               (_, _, f, _) -> f

kcvClosedMapper :: KiCoMapper p p' () Maybe
kcvClosedMapper = KiCoMapper { kcm_kibinder = \_ _ _ -> panic "kcvClosedMapper"
                             , kcm_mkcm = mkcvClosedMapper
                             }

mkcvClosedMapper :: MKiCoMapper p p' () Maybe
mkcvClosedMapper = MKiCoMapper { mkcm_kivar = \_ _ -> Nothing
                               , mkcm_covar = \_ _ -> Nothing
                               , mkcm_hole = \_ _ -> panic "impossible"
                               }

{- *********************************************************************
*                                                                      *
                      KiVarKi
*                                                                      *
********************************************************************* -}

-- Simple Kind Getters
class SKG kind where
  getKiVar_maybe :: kind p -> Maybe (KiVar p)

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

chooseFunKiFlag :: MonoKind p -> MonoKind p -> FunKiFlag
chooseFunKiFlag arg_ki res_ki
  | KiPredApp {} <- res_ki
  = pprPanic "chooseFunKiFlag" (text "res_ki =" <+> ppr res_ki)
  | KiPredApp {} <- arg_ki
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

splitMonoFunKis :: MonoKind kv -> ([MonoKind kv], MonoKind kv)
splitMonoFunKis ki = split [] ki
  where
    split args (FunKi _ arg res) = split (arg : args) res
    split args res = (reverse args, res)

mkKiPredApp :: KiPredCon -> MonoKind kv -> MonoKind kv -> MonoKind kv
mkKiPredApp = KiPredApp

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

splitPiKi_maybe
  :: Kind p
  -> Maybe (Either (KiVar p, Kind p) (FunKiFlag, MonoKind p, MonoKind p))
splitPiKi_maybe ki = case ki of
  ForAllKi kv ki -> Just $ Left (kv, ki)
  Mono (FunKi { fk_f = af, fk_arg = arg, fk_res = res }) -> Just $ Right (af, arg, res)
  _ -> Nothing

isMonoFunKi :: MonoKind p -> Bool
isMonoFunKi (FunKi {}) = True
isMonoFunKi _ = False

splitForAllKi_maybe :: Kind p -> Maybe (KiVar p, Kind p)
splitForAllKi_maybe ki = case ki of
  ForAllKi kv ki -> Just (kv, ki)
  _ -> Nothing

splitForAllKiVars :: Kind p -> ([KiVar p], MonoKind p)
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

splitMonoPiKis :: MonoKind kv -> ([PiKiBinder kv], MonoKind kv)
splitMonoPiKis ki = split ki []
  where
    split (FunKi af arg res) bs = split res (Anon arg af : bs)
    split res bs = (reverse bs, res)

splitInvisFunKis :: MonoKind kv -> ([MonoKind kv], MonoKind kv)
splitInvisFunKis ki = split ki []
  where
    split (FunKi { fk_f = f, fk_arg = arg, fk_res = res }) bs
      | isInvisibleKiFunArg f = split res (arg:bs)
    split ki bs = (reverse bs, ki)

mkForAllKis :: [KiVar p] -> Kind p -> Kind p
mkForAllKis kis ki = foldr ForAllKi ki kis

mkForAllKisMono :: [KiVar p] -> MonoKind p -> Kind p
mkForAllKisMono kis mki = foldr ForAllKi (Mono mki) kis

isAtomicKi :: MonoKind kv -> Bool
isAtomicKi (KiVarKi {}) = True
isAtomicKi (BIKi {}) = True
isAtomicKi _ = False

isForAllKi :: Kind kv -> Bool
isForAllKi ForAllKi{} = True
isForAllKi Mono{} = False
