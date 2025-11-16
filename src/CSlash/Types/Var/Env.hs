module CSlash.Types.Var.Env where

import qualified GHC.Data.Word64Map.Strict as Word64Map

import CSlash.Types.Name.Occurrence
import CSlash.Types.Name
import CSlash.Types.Var as Var
import CSlash.Types.Var.Set
import CSlash.Types.Unique.Set
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.DFM
import CSlash.Types.Unique
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Data.Maybe
import CSlash.Utils.Outputable

{- *********************************************************************
*                                                                      *
                In-scope sets
*                                                                      *
********************************************************************* -}

newtype InScopeSet a = InScope (MkVarSet a)

instance (NamedThing a, Outputable a) => Outputable (InScopeSet a) where
  ppr (InScope s) = text "InScope" <+>
                    braces (fsep (map (ppr . getName) (nonDetEltsUniqSet s)))

emptyInScopeSet :: InScopeSet a
emptyInScopeSet = InScope emptyVarSet

getInScopeVars :: InScopeSet a -> MkVarSet a
getInScopeVars (InScope vs) = vs

mkInScopeSet :: MkVarSet a -> InScopeSet a
mkInScopeSet in_scope = InScope in_scope

extendInScopeSet :: Uniquable a => InScopeSet a -> a -> InScopeSet a
extendInScopeSet (InScope in_scope) v
  = InScope (extendVarSet in_scope v)

extendInScopeSetList :: Uniquable a => InScopeSet a -> [a] -> InScopeSet a
extendInScopeSetList (InScope in_scope) vs
   = InScope $ foldl' extendVarSet in_scope vs

extendInScopeSetSet :: InScopeSet a -> MkVarSet a -> InScopeSet a
extendInScopeSetSet (InScope is) vs = InScope (is `unionVarSet`  vs)

elemInScopeSet :: Uniquable a => a -> InScopeSet a -> Bool
elemInScopeSet v (InScope in_scope) = v `elemVarSet` in_scope

lookupInScope :: Uniquable a => InScopeSet a -> a -> Maybe a
lookupInScope (InScope in_scope) v = lookupVarSet in_scope v

uniqAway :: VarHasUnique a => InScopeSet a -> a -> a
uniqAway in_scope var
  | var `elemInScopeSet` in_scope = uniqAway' in_scope var
  | otherwise = var

uniqAway' :: VarHasUnique a => InScopeSet a -> a -> a
uniqAway' in_scope var
  = setVarUnique var (unsafeGetFreshLocalUnique in_scope)

unsafeGetFreshLocalUnique :: InScopeSet a -> Unique
unsafeGetFreshLocalUnique (InScope set)
  | Just (uniq, _) <- Word64Map.lookupLT (getKey maxLocalUnique) (ufmToIntMap $ getUniqSet set)
  , let uniq' = mkLocalUnique uniq
  , not $ uniq' `ltUnique` minLocalUnique
  = incrUnique uniq'
  | otherwise
  = minLocalUnique

{- *********************************************************************
*                                                                      *
                Dual renaming
*                                                                      *
********************************************************************* -}

data RnEnv2 v = RV2
  { envL :: MkVarEnv v v
  , envR :: MkVarEnv v v
  , in_scope :: InScopeSet v
  }

mkRnEnv2 :: InScopeSet v -> RnEnv2 v
mkRnEnv2 vars = RV2 { envL     = emptyVarEnv
                    , envR     = emptyVarEnv
                    , in_scope = vars }

extendRnInScopeSetList :: Uniquable v => RnEnv2 v -> [v] -> RnEnv2 v
extendRnInScopeSetList env vs
  | null vs   = env
  | otherwise = env { in_scope = extendInScopeSetList (in_scope env) vs }

rnInScope :: Uniquable v => v -> RnEnv2 v -> Bool
rnInScope x env = x `elemInScopeSet` in_scope env

rnInScopeSet :: RnEnv2 v -> InScopeSet v
rnInScopeSet = in_scope

rnEnvL :: RnEnv2 v -> MkVarEnv v v
rnEnvL = envL

rnEnvR :: RnEnv2 v -> MkVarEnv v v
rnEnvR = envR

rnBndrs2 :: VarHasUnique v => RnEnv2 v -> [v] -> [v] -> RnEnv2 v
rnBndrs2 env bsL bsR = foldl2 rnBndr2 env bsL bsR

rnBndr2 :: VarHasUnique v => RnEnv2 v -> v -> v -> RnEnv2 v
rnBndr2 env bL bR = fst $ rnBndr2_var env bL bR

rnBndr2_var :: VarHasUnique v => RnEnv2 v -> v -> v -> (RnEnv2 v, v)
rnBndr2_var (RV2 { envL = envL, envR = envR, in_scope = in_scope }) bL bR
  = ( RV2 { envL = extendVarEnv envL bL new_b
          , envR = extendVarEnv envR bR new_b
          , in_scope = extendInScopeSet in_scope new_b }
    , new_b)
  where
    new_b | not (bR `elemInScopeSet` in_scope) = bR
          | not (bL `elemInScopeSet` in_scope) = bR `setVarUnique` varUnique bL
          | otherwise                          = uniqAway' in_scope bR

rnBndrL :: VarHasUnique v => RnEnv2 v -> v -> (RnEnv2 v, v)
rnBndrL (RV2 { envL = envL, envR = envR, in_scope = in_scope }) bL
  = ( RV2 { envL     = extendVarEnv envL bL new_b
          , envR     = envR
          , in_scope = extendInScopeSet in_scope new_b }
    , new_b)
  where
    new_b = uniqAway in_scope bL

rnBndrR :: VarHasUnique v => RnEnv2 v -> v -> (RnEnv2 v, v)
rnBndrR (RV2 { envL = envL, envR = envR, in_scope = in_scope }) bR
  = ( RV2 { envR     = extendVarEnv envR bR new_b
          , envL     = envL
          , in_scope = extendInScopeSet in_scope new_b }
    , new_b)
  where
    new_b = uniqAway in_scope bR

rnEtaL :: VarHasUnique v => RnEnv2 v -> v -> (RnEnv2 v, v)
rnEtaL (RV2 { envL = envL, envR = envR, in_scope = in_scope }) bL
  = ( RV2 { envL     = extendVarEnv envL bL new_b
          , envR     = extendVarEnv envR new_b new_b
          , in_scope = extendInScopeSet in_scope new_b }
    , new_b)
  where
    new_b = uniqAway in_scope bL

rnEtaR :: VarHasUnique v => RnEnv2 v -> v -> (RnEnv2 v, v)
rnEtaR (RV2 { envL = envL, envR = envR, in_scope = in_scope }) bR
  = ( RV2 { envL     = extendVarEnv envL new_b new_b
          , envR     = extendVarEnv envR bR new_b
          , in_scope = extendInScopeSet in_scope new_b }
    , new_b)
  where
    new_b = uniqAway in_scope bR

delBndrL :: Uniquable v => RnEnv2 v -> v -> RnEnv2 v
delBndrL rn@(RV2 { envL = env, in_scope = in_scope }) v
  = rn { envL = env `delVarEnv` v, in_scope = in_scope `extendInScopeSet` v }

delBndrR :: Uniquable v => RnEnv2 v -> v -> RnEnv2 v
delBndrR rn@(RV2 { envR = env, in_scope = in_scope }) v
  = rn { envR = env `delVarEnv` v, in_scope = in_scope `extendInScopeSet` v }

delBndrsL :: Uniquable v => RnEnv2 v -> [v] -> RnEnv2 v
delBndrsL rn@(RV2 { envL = env, in_scope = in_scope }) v
  = rn { envL = env `delVarEnvList` v, in_scope = in_scope `extendInScopeSetList` v }

delBndrsR :: Uniquable v => RnEnv2 v -> [v] -> RnEnv2 v
delBndrsR rn@(RV2 { envR = env, in_scope = in_scope }) v
  = rn { envR = env `delVarEnvList` v, in_scope = in_scope `extendInScopeSetList` v }

rnOccL :: Uniquable v => RnEnv2 v -> v -> v
rnOccL (RV2 { envL = env }) v = lookupVarEnv env v `orElse` v

rnOccR :: Uniquable v => RnEnv2 v -> v -> v
rnOccR (RV2 { envR = env }) v = lookupVarEnv env v `orElse` v

rnOccL_maybe :: Uniquable v => RnEnv2 v -> v -> Maybe v
rnOccL_maybe (RV2 { envL = env }) v = lookupVarEnv env v

rnOccR_maybe :: Uniquable v => RnEnv2 v -> v -> Maybe v
rnOccR_maybe (RV2 { envR = env }) v = lookupVarEnv env v

inRnEnvL :: Uniquable v => RnEnv2 v -> v -> Bool
inRnEnvL (RV2 { envL = env }) v = v `elemVarEnv` env

inRnEnvR :: Uniquable v => RnEnv2 v -> v -> Bool
inRnEnvR (RV2 { envR = env }) v = v `elemVarEnv` env

anyInRnEnvR :: Uniquable v => RnEnv2 v -> MkVarSet v -> Bool
anyInRnEnvR (RV2 { envR = env }) vs
  | isEmptyVarEnv env = False
  | otherwise         = anyVarSet (`elemVarEnv` env) vs

lookupRnInScope :: Uniquable v => RnEnv2 v -> v -> v
lookupRnInScope env v = lookupInScope (in_scope env) v `orElse` v

nukeRnEnvL :: RnEnv2 v -> RnEnv2 v
nukeRnEnvL env = env { envL = emptyVarEnv }

nukeRnEnvR :: RnEnv2 v -> RnEnv2 v
nukeRnEnvR env = env { envR = emptyVarEnv }

rnSwap :: RnEnv2 v -> RnEnv2 v
rnSwap (RV2 { envL = envL, envR = envR, in_scope = in_scope })
  = RV2 { envL = envR, envR = envL, in_scope = in_scope }

{- *********************************************************************
*                                                                      *
                Tidying
*                                                                      *
********************************************************************* -}

type AnyTidyEnv = MkTidyEnv (AnyTyVar AnyKiVar) AnyKiVar

type MkTidyEnv tv kv = ( TidyOccEnv
                       , MkVarEnv tv tv
                       , MkVarEnv kv kv )

emptyTidyEnv :: MkTidyEnv tv kv
emptyTidyEnv = (emptyTidyOccEnv, emptyVarEnv, emptyVarEnv)

mkEmptyTidyEnv :: TidyOccEnv -> MkTidyEnv tv kv
mkEmptyTidyEnv occ_env = (occ_env, emptyVarEnv, emptyVarEnv)

{- *********************************************************************
*                                                                      *
   VarEnv
*                                                                      *
********************************************************************* -}

type MkVarEnv var elt = UniqFM var elt

type VarEnv elt = UniqFM Var elt

type IdEnv elt = UniqFM Id elt

type TyVarEnv elt = UniqFM Var elt

type KiVarEnv elt = UniqFM Var elt

mkVarEnv :: Uniquable var => [(var, a)] -> MkVarEnv var a
mkVarEnv = listToUFM

mapVarEnv :: (a -> b) -> MkVarEnv var a -> MkVarEnv var b
mapVarEnv = mapUFM

emptyVarEnv :: MkVarEnv var a
emptyVarEnv = emptyUFM

delVarEnvList :: Uniquable var => MkVarEnv var a -> [var] -> MkVarEnv var a
delVarEnvList = delListFromUFM

isEmptyVarEnv :: MkVarEnv v a -> Bool
isEmptyVarEnv = isNullUFM

elemVarEnv :: Uniquable v => v -> MkVarEnv v a -> Bool
elemVarEnv = elemUFM

varSetInScope :: MkVarSet v -> InScopeSet v -> Bool
varSetInScope vars (InScope s1) = vars `subVarSet` s1

extendVarEnv :: Uniquable v => MkVarEnv v a -> v -> a -> MkVarEnv v a
extendVarEnv = addToUFM

extendVarEnvList :: Uniquable v => MkVarEnv v a -> [(v, a)] -> MkVarEnv v a
extendVarEnvList = addListToUFM

delVarEnv :: Uniquable v => MkVarEnv v a -> v -> MkVarEnv v a
delVarEnv = delFromUFM

lookupVarEnv :: Uniquable v => MkVarEnv v a -> v -> Maybe a
{-# INLINE lookupVarEnv #-}
lookupVarEnv = lookupUFM

lookupVarEnv_Directly :: MkVarEnv v a -> Unique -> Maybe a
lookupVarEnv_Directly = lookupUFM_Directly

{- *********************************************************************
*                                                                      *
   Deterministic VarEnv (DVarEnv)
*                                                                      *
********************************************************************* -}

type MkDVarEnv var elt = UniqDFM var elt

emptyDVarEnv :: MkDVarEnv v a
emptyDVarEnv = emptyUDFM

dVarEnvElts :: MkDVarEnv v a -> [a]
dVarEnvElts = eltsUDFM

mkDVarEnv :: Uniquable v => [(v, a)] -> MkDVarEnv v a
mkDVarEnv = listToUDFM

extendDVarEnv :: Uniquable v => MkDVarEnv v a -> v -> a -> MkDVarEnv v a
extendDVarEnv = addToUDFM

minusDVarEnv :: MkDVarEnv v a -> MkDVarEnv v a' -> MkDVarEnv v a
minusDVarEnv = minusUDFM

lookupDVarEnv :: Uniquable v => MkDVarEnv v a -> v -> Maybe a
lookupDVarEnv = lookupUDFM

foldDVarEnv :: (a -> b -> b) -> b -> MkDVarEnv v a -> b
foldDVarEnv = foldUDFM

nonDetStrictFoldDVarEnv :: (a -> b -> b) -> b -> MkDVarEnv v a -> b
nonDetStrictFoldDVarEnv = nonDetStrictFoldUDFM

mapDVarEnv :: (a -> b) -> MkDVarEnv v a -> MkDVarEnv v b
mapDVarEnv = mapUDFM

filterDVarEnv :: (a -> Bool) -> MkDVarEnv v a -> MkDVarEnv v a
filterDVarEnv = filterUDFM

alterDVarEnv :: Uniquable v => (Maybe a -> Maybe a) -> MkDVarEnv v a -> v -> MkDVarEnv v a
alterDVarEnv = alterUDFM

plusDVarEnv :: MkDVarEnv v a -> MkDVarEnv v a -> MkDVarEnv v a
plusDVarEnv = plusUDFM

plusDVarEnv_C :: (a -> a -> a) -> MkDVarEnv v a -> MkDVarEnv v a -> MkDVarEnv v a
plusDVarEnv_C = plusUDFM_C

unitDVarEnv :: Uniquable v => v -> a -> MkDVarEnv v a
unitDVarEnv = unitUDFM

delDVarEnv :: Uniquable v => MkDVarEnv v a -> v -> MkDVarEnv v a
delDVarEnv = delFromUDFM

delDVarEnvList :: Uniquable v => MkDVarEnv v a -> [v] -> MkDVarEnv v a
delDVarEnvList = delListFromUDFM

isEmptyDVarEnv :: MkDVarEnv v a -> Bool
isEmptyDVarEnv = isNullUDFM

elemDVarEnv :: Uniquable v => v -> MkDVarEnv v a -> Bool
elemDVarEnv = elemUDFM

extendDVarEnv_C :: Uniquable v => (a -> a -> a) -> MkDVarEnv v a -> v -> a -> MkDVarEnv v a
extendDVarEnv_C = addToUDFM_C

modifyDVarEnv :: Uniquable v => (a -> a) -> MkDVarEnv v a -> v -> MkDVarEnv v a
modifyDVarEnv mangle_fn env key
  = case (lookupDVarEnv env key) of
      Nothing -> env
      Just xx -> extendDVarEnv env key (mangle_fn xx)

partitionDVarEnv :: (a -> Bool) -> MkDVarEnv v a -> (MkDVarEnv v a, MkDVarEnv v a)
partitionDVarEnv = partitionUDFM

extendDVarEnvList :: Uniquable v => MkDVarEnv v a -> [(v, a)] -> MkDVarEnv v a
extendDVarEnvList = addListToUDFM

anyDVarEnv :: (a -> Bool) -> MkDVarEnv v a -> Bool
anyDVarEnv = anyUDFM
