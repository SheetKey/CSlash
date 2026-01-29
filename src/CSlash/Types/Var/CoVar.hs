{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module CSlash.Types.Var.CoVar where

import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import {-# SOURCE #-} CSlash.Core.Kind (MonoKind)
import {-# SOURCE #-} CSlash.Tc.Utils.TcType (TcVarDetails, pprTcVarDetails)

import CSlash.Types.Var.Class

import CSlash.Types.Name hiding (varName)
import CSlash.Types.Unique

import CSlash.Utils.Misc
import CSlash.Utils.Outputable

import Data.Data

data CoVar thing p
  = CoVar
    { cv_name :: !Name
    , cv_real_unique :: {-# UNPACK #-} !Unique
    , cv_thing :: thing p
    }

type KiCoVar = CoVar MonoKind

type TyCoVar = CoVar Type

instance VarHasType TyCoVar

instance VarHasKind (KiCoVar p) p

instance Outputable (thing p) => IsVar (CoVar thing p) 

instance (Typeable thing, Typeable p) => Data (CoVar thing p) where
  toConstr _ = abstractConstr "CoVar"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "CoVar"

instance Outputable (thing p) => Outputable (CoVar thing p)

instance NamedThing (CoVar thing p)

instance Uniquable (CoVar thing p) 

instance Eq (CoVar thing p)

instance Ord (CoVar thing p)

mkCoVar :: Name -> thing p -> CoVar thing p
mkCoVar name thing = CoVar { cv_name = name
                           , cv_real_unique = nameUnique name
                           , cv_thing = thing }

changeCvThingM :: Monad m => (thing p -> m (thing p')) -> CoVar thing p -> m (CoVar thing p')
changeCvThingM f (CoVar name uniq thing) = (CoVar name uniq) <$> f thing

changeCvTypeM :: Monad m => (Type p -> m (Type p')) -> TyCoVar p -> m (TyCoVar p')
changeCvTypeM = changeCvThingM

changCvKindM  :: Monad m => (MonoKind p -> m (MonoKind p')) -> KiCoVar p -> m (KiCoVar p')
changCvKindM = changeCvThingM
