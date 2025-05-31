module CSlash.Types.Var where

import {-# SOURCE #-} CSlash.Types.Name

data Var
instance NamedThing Var
data VarBndr var argf
newtype TyVar
newtype Id
newtype TcTyVar
newtype TcKiVar
