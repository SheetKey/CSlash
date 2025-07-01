{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module CSlash.Types.Var
  ( Var, VarBndr
  , Id
  , TyVar, TcTyVar, AnyTyVar
  , KiVar, TcKiVar, AnyKiVar
  , VarHasKind, AsAnyTy, IsTyVar
  , AsGenericKi
  ) where

import {-# SOURCE #-} CSlash.Types.Name
import Data.Void (Void)

data Var tv kv
instance NamedThing (Var tv kv)
data VarBndr var argf
newtype Id tv kv = Id (Var tv kv)
newtype TyVar kv = TyVar (Var Void kv)
newtype TcTyVar kv = TcTyVar (Var Void kv)
newtype AnyTyVar kv = AnyTyVar (Var Void kv)
newtype KiVar = KiVar (Var Void Void)
newtype TcKiVar = TcKiVar (Var Void Void)
newtype AnyKiVar = AnyKiVar (Var Void Void)

class VarHasKind v kv | v -> kv
class AsAnyTy (thing :: * -> * -> *)
class IsTyVar tv kv | tv -> kv
class AsGenericKi (thing :: * -> *)