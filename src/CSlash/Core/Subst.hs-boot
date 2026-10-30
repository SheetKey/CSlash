{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module CSlash.Core.Subst where

import CSlash.Cs.Pass
import {-# SOURCE #-} CSlash.Types.Var.Id
import {-# SOURCE #-} CSlash.Core.Rep
import {-# SOURCE #-} CSlash.Core.TyCon
import CSlash.Types.Var.TyVar
import CSlash.Types.Var.KiVar
import CSlash.Types.Var.CoVar
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Utils.Outputable
import CSlash.Utils.Misc

fromZkType :: HasPass p pass => Type Zk -> Type p

type role Subst phantom nominal
data Subst p p'

type TermSubstInScope = ( InScopeSet (Id Zk)
                        , InScopeSet (TyCoVar Zk)
                        , InScopeSet (TyVar Zk)
                        , InScopeSet (KiCoVar Zk)
                        , InScopeSet (KiVar Zk) )

type KvSubstEnv p p' = VarEnv (KiVar p) (MonoKind p')

class SubstP p p' where
  vacuous_kv :: KiVar p -> KiVar p'

  vacuous_set_tv_kind :: MonoKind p' -> TyVar p -> TyVar p'
  vacuous_set_kcv_kind :: MonoKind p' -> KiCoVar p -> KiCoVar p'

  vacuous_tycon :: TyCon p -> TyCon p'

instance {-# INCOHERENT #-} SubstP Zk p 
instance {-# INCOHERENT #-} SubstP p Tc 
instance SubstP p p 

mkEmptySubst
  :: (HasPass p pass, HasPass p' pass', SubstP p p')
  => (TyVarSet p, KiCoVarSet p, KiVarSet p)    -- domain FVs
  -> (TyVarSet p', KiCoVarSet p', KiVarSet p') -- range FVs
  -> Subst p p'

noDomFVs
  :: (Outputable thing, HasPass p pass) => thing
  -> (TyVarSet p, KiCoVarSet p, KiVarSet p)
  -> (TyVarSet p, KiCoVarSet p, KiVarSet p)

substTy :: (HasDebugCallStack, HasPass p pass, HasPass p' pass', SubstP p p') => Subst p p' -> Type p -> Type p'

substMonoKi
  :: (HasDebugCallStack, HasPass p pass, HasPass p' pass', SubstP p p')
  => Subst p p' -> MonoKind p -> MonoKind p'

extendTvSubst :: Subst p p' -> TyVar p -> Type p' -> Subst p p'

extendKCvSubst :: Subst p p' -> KiCoVar p -> KindCoercion p' -> Subst p p'

extendKvSubst :: Subst p p' -> KiVar p -> MonoKind p' -> Subst p p'

substTyUnchecked :: (HasPass p pass, HasPass p' pass', SubstP p p') => Subst p p' -> Type p -> Type p'

isEmptySubst :: Subst p p' -> Bool

substMonoKiUnchecked
  :: (HasDebugCallStack, HasPass p pass, HasPass p' pass', SubstP p p')
  => Subst p p' -> MonoKind p -> MonoKind p'

fromZkKind :: HasPass p pass => Kind Zk -> Kind p

substTyVar :: (HasPass p pass, HasPass p' pass') => Subst p p' -> TyVar p -> Type p'

substKiVar
  :: (HasDebugCallStack, HasPass p pass, HasPass p' pass')
  => Subst p p' -> KiVar p -> MonoKind p'

extendSubstInScopeSetsSets :: Subst p p' -> (TyVarSet p', KiCoVarSet p', KiVarSet p') -> Subst p p'

zapSubst :: Subst p p' -> Subst p p'

composeKvSubst
  :: (HasPass p pass, HasPass p' pass')
  => InScopeSet (KiVar p') -> KvSubstEnv p' p' -> Subst p p' -> Subst p p'

extendTvSubstInScope :: Subst p p' -> TyVar p' -> Subst p p'

extendKCvSubstInScope :: Subst p p' -> KiCoVar p' -> Subst p p'

kv_in_scope :: Subst p p' -> InScopeSet (KiVar p')
tv_in_scope :: Subst p p' -> InScopeSet (TyVar p')
kcv_in_scope :: Subst p p' -> InScopeSet (KiCoVar p')

substKiCo :: (HasPass p pass, HasPass p' pass', SubstP p p') => Subst p p' -> KindCoercion p -> KindCoercion p'
