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

newtype InScopeSet a = InScope (VarSet a)

instance (NamedThing a, Outputable a) => Outputable (InScopeSet a) where
  ppr (InScope s) = text "InScope" <+>
                    braces (fsep (map (ppr . getName) (nonDetEltsUniqSet s)))

emptyInScopeSet :: InScopeSet a
emptyInScopeSet = InScope emptyVarSet

getInScopeVars :: InScopeSet a -> VarSet a
getInScopeVars (InScope vs) = vs

mkInScopeSet :: VarSet a -> InScopeSet a
mkInScopeSet in_scope = InScope in_scope

extendInScopeSet :: Uniquable a => InScopeSet a -> a -> InScopeSet a
extendInScopeSet (InScope in_scope) v
  = InScope (extendVarSet in_scope v)

extendInScopeSetList :: Uniquable a => InScopeSet a -> [a] -> InScopeSet a
extendInScopeSetList (InScope in_scope) vs
   = InScope $ foldl' extendVarSet in_scope vs

extendInScopeSetSet :: InScopeSet a -> VarSet a -> InScopeSet a
extendInScopeSetSet (InScope is) vs = InScope (is `unionVarSet`  vs)

elemInScopeSet :: Uniquable a => a -> InScopeSet a -> Bool
elemInScopeSet v (InScope in_scope) = v `elemVarSet` in_scope

lookupInScope :: Uniquable a => InScopeSet a -> a -> Maybe a
lookupInScope (InScope in_scope) v = lookupVarSet in_scope v

lookupInScope_Directly :: InScopeSet a -> Unique -> Maybe a 
lookupInScope_Directly (InScope in_scope) u = lookupUniqSet_Directly in_scope u

uniqAway :: IsVar a => InScopeSet a -> a -> a
uniqAway in_scope var
  | var `elemInScopeSet` in_scope = uniqAway' in_scope var
  | otherwise = var

uniqAway' :: IsVar a => InScopeSet a -> a -> a
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
  { envL :: VarEnv v v
  , envR :: VarEnv v v
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

rnEnvL :: RnEnv2 v -> VarEnv v v
rnEnvL = envL

rnEnvR :: RnEnv2 v -> VarEnv v v
rnEnvR = envR

rnBndrs2 :: IsVar v => RnEnv2 v -> [v] -> [v] -> RnEnv2 v
rnBndrs2 env bsL bsR = foldl2 rnBndr2 env bsL bsR

rnBndr2 :: IsVar v => RnEnv2 v -> v -> v -> RnEnv2 v
rnBndr2 env bL bR = fst $ rnBndr2_var env bL bR

rnBndr2_var :: IsVar v => RnEnv2 v -> v -> v -> (RnEnv2 v, v)
rnBndr2_var (RV2 { envL = envL, envR = envR, in_scope = in_scope }) bL bR
  = ( RV2 { envL = extendVarEnv envL bL new_b
          , envR = extendVarEnv envR bR new_b
          , in_scope = extendInScopeSet in_scope new_b }
    , new_b)
  where
    new_b | not (bR `elemInScopeSet` in_scope) = bR
          | not (bL `elemInScopeSet` in_scope) = bR `setVarUnique` varUnique bL
          | otherwise                          = uniqAway' in_scope bR

rnBndrL :: IsVar v => RnEnv2 v -> v -> (RnEnv2 v, v)
rnBndrL (RV2 { envL = envL, envR = envR, in_scope = in_scope }) bL
  = ( RV2 { envL     = extendVarEnv envL bL new_b
          , envR     = envR
          , in_scope = extendInScopeSet in_scope new_b }
    , new_b)
  where
    new_b = uniqAway in_scope bL

rnBndrR :: IsVar v => RnEnv2 v -> v -> (RnEnv2 v, v)
rnBndrR (RV2 { envL = envL, envR = envR, in_scope = in_scope }) bR
  = ( RV2 { envR     = extendVarEnv envR bR new_b
          , envL     = envL
          , in_scope = extendInScopeSet in_scope new_b }
    , new_b)
  where
    new_b = uniqAway in_scope bR

rnEtaL :: IsVar v => RnEnv2 v -> v -> (RnEnv2 v, v)
rnEtaL (RV2 { envL = envL, envR = envR, in_scope = in_scope }) bL
  = ( RV2 { envL     = extendVarEnv envL bL new_b
          , envR     = extendVarEnv envR new_b new_b
          , in_scope = extendInScopeSet in_scope new_b }
    , new_b)
  where
    new_b = uniqAway in_scope bL

rnEtaR :: IsVar v => RnEnv2 v -> v -> (RnEnv2 v, v)
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

anyInRnEnvR :: Uniquable v => RnEnv2 v -> VarSet v -> Bool
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

type TidyEnv p = ( TidyOccEnv
                 , VarEnv (TyVar p) (TyVar p)
                 , VarEnv (KiCoVar p) (KiCoVar p)
                 , VarEnv (KiVar p) (KiVar p) )

emptyTidyEnv :: TidyEnv p
emptyTidyEnv = (emptyTidyOccEnv, emptyVarEnv, emptyVarEnv, emptyVarEnv)

mkEmptyTidyEnv :: TidyOccEnv -> TidyEnv p
mkEmptyTidyEnv occ_env = (occ_env, emptyVarEnv, emptyVarEnv, emptyVarEnv)

{- *********************************************************************
*                                                                      *
   VarEnv
*                                                                      *
********************************************************************* -}

type VarEnv var elt = UniqFM var elt

mkVarEnv :: Uniquable var => [(var, a)] -> VarEnv var a
mkVarEnv = listToUFM

mapVarEnv :: (a -> b) -> VarEnv var a -> VarEnv var b
mapVarEnv = mapUFM

emptyVarEnv :: VarEnv var a
emptyVarEnv = emptyUFM

delVarEnvList :: Uniquable var => VarEnv var a -> [var] -> VarEnv var a
delVarEnvList = delListFromUFM

isEmptyVarEnv :: VarEnv v a -> Bool
isEmptyVarEnv = isNullUFM

elemVarEnv :: Uniquable v => v -> VarEnv v a -> Bool
elemVarEnv = elemUFM

varSetInScope :: VarSet v -> InScopeSet v -> Bool
varSetInScope vars (InScope s1) = vars `subVarSet` s1

extendVarEnv :: Uniquable v => VarEnv v a -> v -> a -> VarEnv v a
extendVarEnv = addToUFM

extendVarEnvList :: Uniquable v => VarEnv v a -> [(v, a)] -> VarEnv v a
extendVarEnvList = addListToUFM

delVarEnv :: Uniquable v => VarEnv v a -> v -> VarEnv v a
delVarEnv = delFromUFM

lookupVarEnv :: Uniquable v => VarEnv v a -> v -> Maybe a
{-# INLINE lookupVarEnv #-}
lookupVarEnv = lookupUFM

lookupVarEnv_Directly :: VarEnv v a -> Unique -> Maybe a
lookupVarEnv_Directly = lookupUFM_Directly

{- *********************************************************************
*                                                                      *
   Deterministic VarEnv (DVarEnv)
*                                                                      *
********************************************************************* -}

type DVarEnv var elt = UniqDFM var elt

emptyDVarEnv :: DVarEnv v a
emptyDVarEnv = emptyUDFM

dVarEnvElts :: DVarEnv v a -> [a]
dVarEnvElts = eltsUDFM

mkDVarEnv :: Uniquable v => [(v, a)] -> DVarEnv v a
mkDVarEnv = listToUDFM

extendDVarEnv :: Uniquable v => DVarEnv v a -> v -> a -> DVarEnv v a
extendDVarEnv = addToUDFM

minusDVarEnv :: DVarEnv v a -> DVarEnv v a' -> DVarEnv v a
minusDVarEnv = minusUDFM

lookupDVarEnv :: Uniquable v => DVarEnv v a -> v -> Maybe a
lookupDVarEnv = lookupUDFM

foldDVarEnv :: (a -> b -> b) -> b -> DVarEnv v a -> b
foldDVarEnv = foldUDFM

nonDetStrictFoldDVarEnv :: (a -> b -> b) -> b -> DVarEnv v a -> b
nonDetStrictFoldDVarEnv = nonDetStrictFoldUDFM

mapDVarEnv :: (a -> b) -> DVarEnv v a -> DVarEnv v b
mapDVarEnv = mapUDFM

filterDVarEnv :: (a -> Bool) -> DVarEnv v a -> DVarEnv v a
filterDVarEnv = filterUDFM

alterDVarEnv :: Uniquable v => (Maybe a -> Maybe a) -> DVarEnv v a -> v -> DVarEnv v a
alterDVarEnv = alterUDFM

plusDVarEnv :: DVarEnv v a -> DVarEnv v a -> DVarEnv v a
plusDVarEnv = plusUDFM

plusDVarEnv_C :: (a -> a -> a) -> DVarEnv v a -> DVarEnv v a -> DVarEnv v a
plusDVarEnv_C = plusUDFM_C

unitDVarEnv :: Uniquable v => v -> a -> DVarEnv v a
unitDVarEnv = unitUDFM

delDVarEnv :: Uniquable v => DVarEnv v a -> v -> DVarEnv v a
delDVarEnv = delFromUDFM

delDVarEnvList :: Uniquable v => DVarEnv v a -> [v] -> DVarEnv v a
delDVarEnvList = delListFromUDFM

isEmptyDVarEnv :: DVarEnv v a -> Bool
isEmptyDVarEnv = isNullUDFM

elemDVarEnv :: Uniquable v => v -> DVarEnv v a -> Bool
elemDVarEnv = elemUDFM

extendDVarEnv_C :: Uniquable v => (a -> a -> a) -> DVarEnv v a -> v -> a -> DVarEnv v a
extendDVarEnv_C = addToUDFM_C

modifyDVarEnv :: Uniquable v => (a -> a) -> DVarEnv v a -> v -> DVarEnv v a
modifyDVarEnv mangle_fn env key
  = case (lookupDVarEnv env key) of
      Nothing -> env
      Just xx -> extendDVarEnv env key (mangle_fn xx)

partitionDVarEnv :: (a -> Bool) -> DVarEnv v a -> (DVarEnv v a, DVarEnv v a)
partitionDVarEnv = partitionUDFM

extendDVarEnvList :: Uniquable v => DVarEnv v a -> [(v, a)] -> DVarEnv v a
extendDVarEnvList = addListToUDFM

anyDVarEnv :: (a -> Bool) -> DVarEnv v a -> Bool
anyDVarEnv = anyUDFM
