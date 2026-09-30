{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Core.Kind
  ( module CSlash.Core.Kind
  , module CSlash.Core.Rep
  , KiVar
  , Name
  ) where

import Prelude hiding ((<>))

import {-# SOURCE #-} CSlash.Types.Var
import {-# SOURCE #-} CSlash.Core.Kind.Compare (eqMonoKind)

import CSlash.Core.Rep
import {-# SOURCE #-} CSlash.Core.Mapper

import CSlash.Cs.Pass

import CSlash.Types.Var.Env
import CSlash.Types.Var.Set

import CSlash.Types.Basic
import CSlash.Types.Unique
import CSlash.Types.Name
import CSlash.Types.Name.Env
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
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe (isJust)

{- **********************************************************************
*                                                                       *
                        Kind
*                                                                       *
********************************************************************** -}

type RowSigEnv p = RowEnv' (RowSig p)
type ZipRowSigEnv p = RowEnv' (RowSig p, RowSig p)
type TyRowEnv p = RowEnv' (Type p)
newtype RowEnv' a = RowEnv (OccEnv a)

mkTyRowEnv :: [(Name, Type p)] -> TyRowEnv p
mkTyRowEnv pairs = RowEnv $ extendOccEnvList emptyOccEnv pairs'
  where
    pairs' = mapFst (setOccNameSpace (TcRowName (fsLit "")) . nameOccName) pairs

rowEnvElts :: RowEnv' a -> [a]
rowEnvElts (RowEnv e) = nonDetOccEnvElts e

flattenKiCon :: KiCon p -> (MonoKind p, RowSigEnv p)
flattenKiCon = go (RowEnv emptyOccEnv) . KiConApp
  where
    go env (KiConApp (KiCon _ base rows))
      = go (mkRowSigEnvFromSig rows `plusRowEnv` env) base
    go env base = (base, env)

-- Looks deeply through kicons.
mkRowSigEnv :: MonoKind p -> RowSigEnv p
mkRowSigEnv (KiConApp (KiCon _ base rows))
  = mkRowSigEnv base `plusRowEnv` mkRowSigEnvFromSig rows
mkRowSigEnv _ = RowEnv emptyOccEnv
 
plusRowEnv :: RowEnv' a -> RowEnv' a -> RowEnv' a
plusRowEnv (RowEnv env1) (RowEnv env2) = RowEnv $ env1 `plusOccEnv` env2

mkRowSigEnvFromSig :: [RowSig p] -> RowSigEnv p
mkRowSigEnvFromSig rows
  = RowEnv $ extendOccEnvList emptyOccEnv pairs
  where
    pairs = mkPair <$> rows
    -- mkPair :: RowSig p -> (OccName, RowSig p)
    mkPair r@(RowTySig nm _) = (setOccNameSpace (RowName (fsLit "")) (nameOccName nm), r)
    mkPair r@(RowKiSig nm _) = (setOccNameSpace (TcRowName (fsLit "")) (nameOccName nm), r)

zipRowSigEnvs :: RowSigEnv p -> RowSigEnv p -> (RowSigEnv p, RowSigEnv p, ZipRowSigEnv p)
zipRowSigEnvs (RowEnv a) (RowEnv b) =
  let l = a `minusOccEnv` b
      r = b `minusOccEnv` a
      z = intersectOccEnv_C (,) a b
  in (RowEnv l, RowEnv r, RowEnv z)

lookupRowEnv :: RowEnv' a -> Name -> Maybe a
lookupRowEnv (RowEnv env) nm =
  let occ = nameOccName nm
      new_ns = case occNameSpace occ of
                 RowName _ -> RowName (fsLit "")
                 TcRowName _ -> TcRowName (fsLit "")
                 _ -> pprPanic "lookupRowEnv" (ppr nm) -- This means a namespace was set incorrectly elsewhere!
      new_occ = setOccNameSpace new_ns occ
  in lookupOccEnv env new_occ

instance Outputable a => Outputable (RowEnv' a) where
  ppr (RowEnv env) = ppr env

rowSigName :: RowSig p -> Name
rowSigName (RowTySig nm _) = nm
rowSigName (RowKiSig nm _) = nm

kiConName :: KiCon p -> Name
kiConName KiCon{ kicon_name = name }
  | Just n <- name
  = n
  | otherwise
  = panic "kiConName"

-- Only for the TOP kicon. 
kiConRowNames :: KiCon p -> NonEmpty Name
kiConRowNames KiCon{ kicon_rows = rows }
  | r:rs <- rows
  = rowName r :| map rowName rs
  | otherwise
  = panic "kiConRowNames empty rows"

rowName :: RowSig p -> Name
rowName (RowTySig n _) = n
rowName (RowKiSig n _) = n

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

mkFunKi :: HasPass p pass => FunKiFlag -> MonoKind p -> MonoKind p -> MonoKind p
mkFunKi f arg res = assertPpr (f == chooseFunKiFlag arg res)
                    (vcat [ text "f" <+> ppr f
                          , text "chooseF" <+> ppr (chooseFunKiFlag arg res)
                          , text "arg" <+> ppr arg
                          , text "res" <+> ppr res ])
                    $ FunKi { fk_f = f, fk_arg = arg, fk_res = res }

mkFunKi_nc :: FunKiFlag -> MonoKind kv -> MonoKind kv -> MonoKind kv
mkFunKi_nc f arg res = FunKi { fk_f = f, fk_arg = arg, fk_res = res }

mkVisFunKis :: HasPass p pass => [MonoKind p] -> MonoKind p -> MonoKind p
mkVisFunKis args res = foldr (mkFunKi FKF_K_K) res args

mkInvisFunKis :: HasPass p pass => [MonoKind p] -> MonoKind p -> MonoKind p
mkInvisFunKis args res = foldr (mkFunKi FKF_C_K) res args

mkInvisFunKis_nc :: [MonoKind p] -> MonoKind p -> MonoKind p
mkInvisFunKis_nc args res = foldr (mkFunKi_nc FKF_C_K) res args

mkForAllKi :: KiVar p -> Kind p -> Kind p
mkForAllKi = ForAllKi

mkPiKi :: (HasDebugCallStack, HasPass p pass) => PiKiBinder p -> Kind p -> Kind p
mkPiKi (Anon ki1 af) (Mono ki2) = Mono $ mkFunKi af ki1 ki2
mkPiKi (Named bndr) ki = mkForAllKi bndr ki
mkPiKi other_b other_k = pprPanic "mkPiKi" (panic "ppr other_b $$ ppr other_k")

mkPiKis :: (HasDebugCallStack, HasPass p pass) => [PiKiBinder p] -> Kind p -> Kind p
mkPiKis kbs ki = foldr mkPiKi ki kbs

{- *********************************************************************
*                                                                      *
                Coercions
*                                                                      *
********************************************************************* -}

mkReflRowCo :: RowSig p -> RowCoercion p 
mkReflRowCo (RowTySig nm ty) = RowTySigCo nm (mkReflTyCo ty)
mkReflRowCo (RowKiSig nm ki) = RowKiSigCo nm (mkReflKiCo ki)

isReflRowCo :: RowCoercion p -> Bool
isReflRowCo (RowTySigCo _ co) = isReflTyCo co
isReflRowCo (RowKiSigCo _ co) = isReflKiCo co

isReflRowCo_maybe :: HasPass p pass => RowCoercion p -> Maybe (RowSig p)
isReflRowCo_maybe (RowTySigCo nm co) = RowTySig nm <$> isReflTyCo_maybe co
isReflRowCo_maybe (RowKiSigCo nm co) = RowKiSig nm <$> isReflKiCo_maybe co

mkKiRowCo :: HasPass p pass => KindCoercion p -> [RowCoercion p] -> KindCoercion p
mkKiRowCo base rs
  | Just bk <- isReflKiCo_maybe base
  , let rks = isReflRowCo_maybe <$> rs
  , Just rks' <- sequence rks
  = mkReflKiCo $ KiConApp (KiCon Nothing bk rks')
  | otherwise
  = KiRowCo base rs

coHoleCoVar :: KindCoercionHole -> TcKiCoVar 
coHoleCoVar = kch_co_var

mkSelCo
  :: (HasDebugCallStack, HasPass p pass) => CoSel -> KindCoercion p -> KindCoercion p
mkSelCo n co = mkSelCo_maybe n co `orElse` SelCo n co

mkSelCo_maybe
  :: (HasDebugCallStack, HasPass p pass) => CoSel -> KindCoercion p -> Maybe (KindCoercion p)
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

selectFromKind :: (HasDebugCallStack, HasPass p pass) => CoSel -> MonoKind p -> MonoKind p
selectFromKind (SelFun SelArg) ki
  | Just (_, arg, _) <- splitMonoFunKi_maybe ki
  = arg
selectFromKind  (SelFun SelRes) ki
  | Just (_, _, res) <- splitMonoFunKi_maybe ki
  = res
selectFromKind cs ki = pprPanic "selectFromKind" (ppr cs $$ ppr ki)

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
  :: HasPass p pass
  => FunKiFlag
  -> KindCoercion p
  -> KindCoercion p
  -> KindCoercion p
mkFunKiCo af arg_co res_co = mkFunKiCo2 af af arg_co res_co

mkFunKiCo2
  :: HasPass p pass
  => FunKiFlag
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

kiCoercionParts :: HasPass p pass => KindCoercion p -> (KiPredCon, Pair (MonoKind p))
kiCoercionParts co = (kiCoercionPred co, Pair (kicoercionLKind co) (kicoercionRKind co))

kiCoercionKind :: HasPass p pass => KindCoercion p -> MonoKind p
kiCoercionKind co = case kiCoercionParts co of
  (pred, Pair k1 k2) -> mkKiPredApp pred k1 k2

kiCoercionPred :: HasPass p pass => KindCoercion p -> KiPredCon
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
    -- go (KiPredAppCo{}) = panic "kiCoercionPred/KiPredAppCo"
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

kicoercionLKind :: HasPass p pass => KindCoercion p -> MonoKind p
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

kicoercionRKind :: HasPass p pass => KindCoercion p -> MonoKind p
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

kiCoVarKiPred :: (HasDebugCallStack, Outputable cv, VarHasKind cv p, HasPass p pass) => cv -> KiPredCon
kiCoVarKiPred cv | (kc, _, _) <- coVarKinds cv = kc

coVarLKind :: (HasDebugCallStack, Outputable cv, VarHasKind cv p, HasPass p pass) => cv -> MonoKind p
coVarLKind cv | (_, ki1, _) <- coVarKinds cv = ki1

coVarRKind :: (HasDebugCallStack, Outputable cv, VarHasKind cv p, HasPass p pass) => cv -> MonoKind p
coVarRKind cv | (_, _, ki2) <- coVarKinds cv = ki2

coVarKinds
  :: (HasDebugCallStack, Outputable cv, VarHasKind cv p, HasPass p pass)
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

chooseFunKiFlag :: HasPass p pass => MonoKind p -> MonoKind p -> FunKiFlag
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

mkKiPredAppCo :: KiPredCon -> KindCoercion p -> KindCoercion p -> KindCoercion p
mkKiPredAppCo pred co1 co2
  | Just ki1 <- isReflKiCo_maybe co1
  , Just ki2 <- isReflKiCo_maybe co2
  = mkReflKiCo $ mkKiPredApp pred ki1 ki2
  | otherwise = panic "KiPredAppCo pred co1 co2"

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

{- *********************************************************************
*                                                                      *
        Sequencing on kinds
*                                                                      *
********************************************************************* -}

seqMonoKind :: MonoKind Zk -> ()
seqMonoKind (KiVarKi kv) = kv `seq` ()
seqMonoKind (BIKi bi) = bi `seq` ()
seqMonoKind (KiPredApp p k1 k2) = p `seq` seqMonoKind k1 `seq` seqMonoKind k2
seqMonoKind (KiConApp{}) = panic "seqMonokind kiconapp"
seqMonoKind (FunKi _ k1 k2) = seqMonoKind k1 `seq` seqMonoKind k2

seqKiCo :: KindCoercion Zk -> ()
seqKiCo (Refl ki) = seqMonoKind ki
seqKiCo BI_U_A = ()
seqKiCo BI_A_L = ()
seqKiCo (BI_U_LTEQ ki) = seqMonoKind ki
seqKiCo (BI_LTEQ_L ki) = seqMonoKind ki
seqKiCo (LiftEq co) = seqKiCo co
seqKiCo (LiftLT co) = seqKiCo co
seqKiCo (FunCo af1 af2 co1 co2) = af1 `seq` af2 `seq` seqKiCo co1 `seq` seqKiCo co2
seqKiCo (KiCoVarCo cv) = cv `seq` ()
seqKiCo (SymCo co) = seqKiCo co
seqKiCo (TransCo co1 co2) = seqKiCo co1 `seq` seqKiCo co2
seqKiCo (SelCo n co) = n `seq` seqKiCo co
