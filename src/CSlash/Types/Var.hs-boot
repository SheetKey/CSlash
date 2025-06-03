module CSlash.Types.Var
  ( Var, VarBndr
  , Id
  , TyVar, TcTyVar, AnyTyVar
  , KiVar, TcKiVar, AnyKiVar
  ) where

import {-# SOURCE #-} CSlash.Types.Name

data Var
instance NamedThing Var
data VarBndr var argf
newtype Id = Id Var
newtype TyVar = TyVar Var
newtype TcTyVar = TcTyVar Var
newtype AnyTyVar = AnyTyVar Var
newtype KiVar = KiVar Var
newtype TcKiVar = TcKiVar Var
newtype AnyKiVar = AnyKiVar Var