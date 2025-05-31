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

newtype InScopeSet = InScope VarSet

instance Outputable InScopeSet where
  ppr (InScope s) = text "InScope" <+>
                    braces (fsep (map (ppr . Var.varName) (nonDetEltsUniqSet s)))

emptyInScopeSet :: InScopeSet
emptyInScopeSet = InScope emptyVarSet

getInScopeVars :: InScopeSet -> VarSet
getInScopeVars (InScope vs) = vs

mkInScopeSet :: VarSet -> InScopeSet
mkInScopeSet in_scope = InScope in_scope

extendInScopeSet :: InScopeSet -> Var -> InScopeSet
extendInScopeSet (InScope in_scope) v
  = InScope (extendVarSet in_scope v)

extendInScopeSetList :: InScopeSet -> [Var] -> InScopeSet
extendInScopeSetList (InScope in_scope) vs
   = InScope $ foldl' extendVarSet in_scope vs

elemInScopeSet :: Var -> InScopeSet -> Bool
elemInScopeSet v (InScope in_scope) = v `elemVarSet` in_scope

lookupInScope :: InScopeSet -> Var -> Maybe Var
lookupInScope (InScope in_scope) v = lookupVarSet in_scope v

uniqAway :: InScopeSet -> Var -> Var
uniqAway in_scope var
  | var `elemInScopeSet` in_scope = uniqAway' in_scope var
  | otherwise = var

uniqAway' :: InScopeSet -> Var -> Var
uniqAway' in_scope var
  = setVarUnique var (unsafeGetFreshLocalUnique in_scope)

unsafeGetFreshLocalUnique :: InScopeSet -> Unique
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

data RnEnv2 = RV2
  { envL :: VarEnv Var
  , envR :: VarEnv Var
  , in_scope :: InScopeSet
  }

mkRnEnv2 :: InScopeSet -> RnEnv2
mkRnEnv2 vars = RV2 { envL     = emptyVarEnv
                    , envR     = emptyVarEnv
                    , in_scope = vars }

extendRnInScopeSetList :: RnEnv2 -> [Var] -> RnEnv2
extendRnInScopeSetList env vs
  | null vs   = env
  | otherwise = env { in_scope = extendInScopeSetList (in_scope env) vs }

rnInScope :: Var -> RnEnv2 -> Bool
rnInScope x env = x `elemInScopeSet` in_scope env

rnInScopeSet :: RnEnv2 -> InScopeSet
rnInScopeSet = in_scope

rnEnvL :: RnEnv2 -> VarEnv Var
rnEnvL = envL

rnEnvR :: RnEnv2 -> VarEnv Var
rnEnvR = envR

rnBndrs2 :: RnEnv2 -> [Var] -> [Var] -> RnEnv2
rnBndrs2 env bsL bsR = foldl2 rnBndr2 env bsL bsR

rnBndr2 :: RnEnv2 -> Var -> Var -> RnEnv2
rnBndr2 env bL bR = fst $ rnBndr2_var env bL bR

rnBndr2_var :: RnEnv2 -> Var -> Var -> (RnEnv2, Var)
rnBndr2_var (RV2 { envL = envL, envR = envR, in_scope = in_scope }) bL bR
  = ( RV2 { envL = extendVarEnv envL bL new_b
          , envR = extendVarEnv envR bR new_b
          , in_scope = extendInScopeSet in_scope new_b }
    , new_b)
  where
    new_b | not (bR `elemInScopeSet` in_scope) = bR
          | not (bL `elemInScopeSet` in_scope) = bR `setVarUnique` varUnique bL
          | otherwise                          = uniqAway' in_scope bR

rnBndrL :: RnEnv2 -> Var -> (RnEnv2, Var)
rnBndrL (RV2 { envL = envL, envR = envR, in_scope = in_scope }) bL
  = ( RV2 { envL     = extendVarEnv envL bL new_b
          , envR     = envR
          , in_scope = extendInScopeSet in_scope new_b }
    , new_b)
  where
    new_b = uniqAway in_scope bL

rnBndrR :: RnEnv2 -> Var -> (RnEnv2, Var)
rnBndrR (RV2 { envL = envL, envR = envR, in_scope = in_scope }) bR
  = ( RV2 { envR     = extendVarEnv envR bR new_b
          , envL     = envL
          , in_scope = extendInScopeSet in_scope new_b }
    , new_b)
  where
    new_b = uniqAway in_scope bR

rnEtaL :: RnEnv2 -> Var -> (RnEnv2, Var)
rnEtaL (RV2 { envL = envL, envR = envR, in_scope = in_scope }) bL
  = ( RV2 { envL     = extendVarEnv envL bL new_b
          , envR     = extendVarEnv envR new_b new_b
          , in_scope = extendInScopeSet in_scope new_b }
    , new_b)
  where
    new_b = uniqAway in_scope bL

rnEtaR :: RnEnv2 -> Var -> (RnEnv2, Var)
rnEtaR (RV2 { envL = envL, envR = envR, in_scope = in_scope }) bR
  = ( RV2 { envL     = extendVarEnv envL new_b new_b
          , envR     = extendVarEnv envR bR new_b
          , in_scope = extendInScopeSet in_scope new_b }
    , new_b)
  where
    new_b = uniqAway in_scope bR

delBndrL :: RnEnv2 -> Var -> RnEnv2
delBndrL rn@(RV2 { envL = env, in_scope = in_scope }) v
  = rn { envL = env `delVarEnv` v, in_scope = in_scope `extendInScopeSet` v }

delBndrR :: RnEnv2 -> Var -> RnEnv2
delBndrR rn@(RV2 { envR = env, in_scope = in_scope }) v
  = rn { envR = env `delVarEnv` v, in_scope = in_scope `extendInScopeSet` v }

delBndrsL :: RnEnv2 -> [Var] -> RnEnv2
delBndrsL rn@(RV2 { envL = env, in_scope = in_scope }) v
  = rn { envL = env `delVarEnvList` v, in_scope = in_scope `extendInScopeSetList` v }

delBndrsR :: RnEnv2 -> [Var] -> RnEnv2
delBndrsR rn@(RV2 { envR = env, in_scope = in_scope }) v
  = rn { envR = env `delVarEnvList` v, in_scope = in_scope `extendInScopeSetList` v }

rnOccL :: RnEnv2 -> Var -> Var
rnOccL (RV2 { envL = env }) v = lookupVarEnv env v `orElse` v

rnOccR :: RnEnv2 -> Var -> Var
rnOccR (RV2 { envR = env }) v = lookupVarEnv env v `orElse` v

rnOccL_maybe :: RnEnv2 -> Var -> Maybe Var
rnOccL_maybe (RV2 { envL = env }) v = lookupVarEnv env v

rnOccR_maybe :: RnEnv2 -> Var -> Maybe Var
rnOccR_maybe (RV2 { envR = env }) v = lookupVarEnv env v

inRnEnvL :: RnEnv2 -> Var -> Bool
inRnEnvL (RV2 { envL = env }) v = v `elemVarEnv` env

inRnEnvR :: RnEnv2 -> Var -> Bool
inRnEnvR (RV2 { envR = env }) v = v `elemVarEnv` env

anyInRnEnvR :: RnEnv2 -> VarSet -> Bool
anyInRnEnvR (RV2 { envR = env }) vs
  | isEmptyVarEnv env = False
  | otherwise         = anyVarSet (`elemVarEnv` env) vs

lookupRnInScope :: RnEnv2 -> Var -> Var
lookupRnInScope env v = lookupInScope (in_scope env) v `orElse` v

nukeRnEnvL :: RnEnv2 -> RnEnv2
nukeRnEnvL env = env { envL = emptyVarEnv }

nukeRnEnvR :: RnEnv2 -> RnEnv2
nukeRnEnvR env = env { envR = emptyVarEnv }

rnSwap :: RnEnv2 -> RnEnv2
rnSwap (RV2 { envL = envL, envR = envR, in_scope = in_scope })
  = RV2 { envL = envR, envR = envL, in_scope = in_scope }

{- *********************************************************************
*                                                                      *
                Tidying
*                                                                      *
********************************************************************* -}

type TidyEnv = (TidyOccEnv, VarEnv Var)

emptyTidyEnv :: TidyEnv
emptyTidyEnv = (emptyTidyOccEnv, emptyVarEnv)

mkEmptyTidyEnv :: TidyOccEnv -> TidyEnv
mkEmptyTidyEnv occ_env = (occ_env, emptyVarEnv)

{- *********************************************************************
*                                                                      *
   VarEnv
*                                                                      *
********************************************************************* -}

type VarEnv elt = UniqFM Var elt

type IdEnv elt = UniqFM Id elt

type TyVarEnv elt = UniqFM Var elt

type KiVarEnv elt = UniqFM Var elt

mkVarEnv :: [(Var, a)] -> VarEnv a
mkVarEnv = listToUFM

mapVarEnv :: (a -> b) -> VarEnv a -> VarEnv b
mapVarEnv = mapUFM

emptyVarEnv :: VarEnv a
emptyVarEnv = emptyUFM

delVarEnvList :: VarEnv a -> [Var] -> VarEnv a
delVarEnvList = delListFromUFM

isEmptyVarEnv :: VarEnv a -> Bool
isEmptyVarEnv = isNullUFM

elemVarEnv :: Var -> VarEnv a -> Bool
elemVarEnv = elemUFM

varSetInScope :: VarSet -> InScopeSet -> Bool
varSetInScope vars (InScope s1) = vars `subVarSet` s1

extendVarEnv :: VarEnv a -> Var -> a -> VarEnv a
extendVarEnv = addToUFM

delVarEnv :: VarEnv a -> Var -> VarEnv a
delVarEnv = delFromUFM

lookupVarEnv :: VarEnv a -> Var -> Maybe a
{-# INLINE lookupVarEnv #-}
lookupVarEnv = lookupUFM

{- *********************************************************************
*                                                                      *
   Deterministic VarEnv (DVarEnv)
*                                                                      *
********************************************************************* -}

type DVarEnv elt = UniqDFM Var elt

emptyDVarEnv :: DVarEnv a
emptyDVarEnv = emptyUDFM

dVarEnvElts :: DVarEnv a -> [a]
dVarEnvElts = eltsUDFM

mkDVarEnv :: [(Var, a)] -> DVarEnv a
mkDVarEnv = listToUDFM

extendDVarEnv :: DVarEnv a -> Var -> a -> DVarEnv a
extendDVarEnv = addToUDFM

minusDVarEnv :: DVarEnv a -> DVarEnv a' -> DVarEnv a
minusDVarEnv = minusUDFM

lookupDVarEnv :: DVarEnv a -> Var -> Maybe a
lookupDVarEnv = lookupUDFM

foldDVarEnv :: (a -> b -> b) -> b -> DVarEnv a -> b
foldDVarEnv = foldUDFM

nonDetStrictFoldDVarEnv :: (a -> b -> b) -> b -> DVarEnv a -> b
nonDetStrictFoldDVarEnv = nonDetStrictFoldUDFM

mapDVarEnv :: (a -> b) -> DVarEnv a -> DVarEnv b
mapDVarEnv = mapUDFM

filterDVarEnv :: (a -> Bool) -> DVarEnv a -> DVarEnv a
filterDVarEnv = filterUDFM

alterDVarEnv :: (Maybe a -> Maybe a) -> DVarEnv a -> Var -> DVarEnv a
alterDVarEnv = alterUDFM

plusDVarEnv :: DVarEnv a -> DVarEnv a -> DVarEnv a
plusDVarEnv = plusUDFM

plusDVarEnv_C :: (a -> a -> a) -> DVarEnv a -> DVarEnv a -> DVarEnv a
plusDVarEnv_C = plusUDFM_C

unitDVarEnv :: Var -> a -> DVarEnv a
unitDVarEnv = unitUDFM

delDVarEnv :: DVarEnv a -> Var -> DVarEnv a
delDVarEnv = delFromUDFM

delDVarEnvList :: DVarEnv a -> [Var] -> DVarEnv a
delDVarEnvList = delListFromUDFM

isEmptyDVarEnv :: DVarEnv a -> Bool
isEmptyDVarEnv = isNullUDFM

elemDVarEnv :: Var -> DVarEnv a -> Bool
elemDVarEnv = elemUDFM

extendDVarEnv_C :: (a -> a -> a) -> DVarEnv a -> Var -> a -> DVarEnv a
extendDVarEnv_C = addToUDFM_C

modifyDVarEnv :: (a -> a) -> DVarEnv a -> Var -> DVarEnv a
modifyDVarEnv mangle_fn env key
  = case (lookupDVarEnv env key) of
      Nothing -> env
      Just xx -> extendDVarEnv env key (mangle_fn xx)

partitionDVarEnv :: (a -> Bool) -> DVarEnv a -> (DVarEnv a, DVarEnv a)
partitionDVarEnv = partitionUDFM

extendDVarEnvList :: DVarEnv a -> [(Var, a)] -> DVarEnv a
extendDVarEnvList = addListToUDFM

anyDVarEnv :: (a -> Bool) -> DVarEnv a -> Bool
anyDVarEnv = anyUDFM
