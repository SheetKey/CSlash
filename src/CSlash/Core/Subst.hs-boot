{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module CSlash.Core.Subst where

import CSlash.Cs.Pass
import {-# SOURCE #-} CSlash.Core.Type.Rep
import {-# SOURCE #-} CSlash.Types.Var.Id
import CSlash.Types.Var.TyVar
import CSlash.Types.Var.KiVar
import CSlash.Types.Var.CoVar
import CSlash.Core.Kind
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

class SubstP p p' 
instance {-# INCOHERENT #-} SubstP Zk p 
instance {-# INCOHERENT #-} SubstP p Tc 
instance SubstP p p 

mkEmptySubst
  :: (HasPass p' pass, SubstP p p')
  => (TyVarSet p, KiCoVarSet p, KiVarSet p)    -- domain FVs
  -> (TyVarSet p', KiCoVarSet p', KiVarSet p') -- range FVs
  -> Subst p p'

noDomFVs
  :: Outputable thing => thing
  -> (TyVarSet p, KiCoVarSet p, KiVarSet p)
  -> (TyVarSet p, KiCoVarSet p, KiVarSet p)

substTy :: (HasDebugCallStack, HasPass p' pass, SubstP p p') => Subst p p' -> Type p -> Type p'

extendTvSubst :: Subst p p' -> TyVar p -> Type p' -> Subst p p'

extendKCvSubst :: Subst p p' -> KiCoVar p -> KindCoercion p' -> Subst p p'

extendKvSubst :: Subst p p' -> KiVar p -> MonoKind p' -> Subst p p'

substTyUnchecked :: (HasPass p' pass, SubstP p p') => Subst p p' -> Type p -> Type p'

isEmptySubst :: Subst p p' -> Bool

substMonoKiUnchecked :: (HasPass p' pass, SubstP p p') => Subst p p' -> MonoKind p -> MonoKind p'

fromZkKind :: HasPass p pass => Kind Zk -> Kind p
