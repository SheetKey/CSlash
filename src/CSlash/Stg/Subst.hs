module CSlash.Stg.Subst where

import CSlash.Core (CoreId)

import CSlash.Types.Var.Id
import CSlash.Types.Var.Env
import CSlash.Utils.Monad.State.Strict

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Trace

data StgSubst = StgSubst (InScopeSet CoreId) StgIdSubstEnv

type StgIdSubstEnv = VarEnv CoreId CoreId

emptySubst :: StgSubst
emptySubst = mkEmptySubst emptyInScopeSet

mkEmptySubst :: InScopeSet CoreId -> StgSubst
mkEmptySubst is = StgSubst is emptyVarEnv

substBndr :: CoreId -> StgSubst -> (CoreId, StgSubst)
substBndr id (StgSubst in_scope env)
  = (new_id, StgSubst new_in_scope new_env)
  where
    new_id = uniqAway in_scope id
    no_change = new_id == id
    new_in_scope = in_scope `extendInScopeSet` new_id
    new_env | no_change = delVarEnv env id
            | otherwise = extendVarEnv env id new_id

substBndrs :: Traversable f => f CoreId -> StgSubst -> (f CoreId, StgSubst)
substBndrs = runState . traverse (state . substBndr)

lookupIdSubst :: HasDebugCallStack => CoreId -> StgSubst -> CoreId
lookupIdSubst id (StgSubst in_scope env)
  | not (isLocalId id) = id
  | Just id' <- lookupVarEnv env id = id'
  | Just id' <- lookupInScope in_scope id = id'
  | otherwise = warnPprTrace True "StgSubst.lookupIdSubst" (ppr id $$ ppr in_scope) id

noWarnLookupIdSubst :: HasDebugCallStack => CoreId -> StgSubst -> CoreId
noWarnLookupIdSubst id (StgSubst in_scope env)
  | not (isLocalId id) = id
  | Just id' <- lookupVarEnv env id = id'
  | Just id' <- lookupInScope in_scope id = id'
  | Just id' <- lookupInScope in_scope id = id'
  | otherwise = id

extendInScope :: CoreId -> StgSubst -> StgSubst
extendInScope id (StgSubst in_scope env) = StgSubst (in_scope `extendInScopeSet` id) env

extendSubst :: CoreId -> CoreId -> StgSubst -> StgSubst
extendSubst id new_id (StgSubst in_scope env)
  = assertPpr (new_id `elemInScopeSet` in_scope) (ppr id <+> ppr new_id $$ ppr in_scope) $
    StgSubst in_scope (extendVarEnv env id new_id)
