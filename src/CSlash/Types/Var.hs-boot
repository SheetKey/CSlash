module CSlash.Types.Var where

import {-# SOURCE #-} CSlash.Types.Name

data Var
instance NamedThing Var
data VarBndr var argf
type TypeVar = Var
type Id = Var
type TcTyVar = Var
