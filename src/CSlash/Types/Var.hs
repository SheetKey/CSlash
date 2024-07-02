module CSlash.Types.Var where

import CSlash.Utils.Misc

import Data.Data

type Id = Var

data Var

instance Eq Var

instance Data Var where
  toConstr _ = abstractConstr "Var"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "Var"
