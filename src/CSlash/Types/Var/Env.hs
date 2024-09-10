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

elemInScopeSet :: Var -> InScopeSet -> Bool
elemInScopeSet v (InScope in_scope) = v `elemVarSet` in_scope

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
                Tidying
*                                                                      *
********************************************************************* -}

type TidyEnv = (TidyOccEnv, VarEnv Var)

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

type KdVarEnv elt = UniqFM Var elt

emptyVarEnv :: VarEnv a
emptyVarEnv = emptyUFM

isEmptyVarEnv :: VarEnv a -> Bool
isEmptyVarEnv = isNullUFM

varSetInScope :: VarSet -> InScopeSet -> Bool
varSetInScope vars (InScope s1) = vars `subVarSet` s1

extendVarEnv :: VarEnv a -> Var -> a -> VarEnv a
extendVarEnv = addToUFM

delVarEnv :: VarEnv a -> Var -> VarEnv a
delVarEnv = delFromUFM

lookupVarEnv :: VarEnv a -> Var -> Maybe a
{-# INLINE lookupVarEnv #-}
lookupVarEnv = lookupUFM
