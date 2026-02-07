{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PatternSynonyms #-}

module CSlash.Types.Var.Class where

import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import {-# SOURCE #-} CSlash.Core.Kind (MonoKind)
import {-# SOURCE #-} CSlash.Types.Name (Name, NamedThing)
import {-# SOURCE #-} CSlash.Tc.Utils.TcType

import CSlash.Types.Unique

import CSlash.Utils.Binary
import CSlash.Utils.Outputable

import Data.Data

{- *********************************************************************
*                                                                      *
*                   ForAllFlag
*                                                                      *
********************************************************************* -}

-- Reduced the number of 'HasPass p pass' constraints needed
class (Eq v, Ord v, {-Outputable v, -}NamedThing v, Uniquable v) => IsVar v where
  varName :: v -> Name
  setVarName :: v -> Name -> v

  varUnique :: v -> Unique
  setVarUnique :: v -> Unique -> v

  isTcVar :: v -> Bool

class VarHasType id p | id -> p where
  varType :: id -> Type p
  setVarType :: id -> Type p -> id
  updateVarType :: (Type p -> Type p) -> id -> id
  updateVarTypeM :: Monad m => (Type p -> m (Type p)) -> id -> m id

class VarHasKind tv p | tv -> p where
  varKind :: tv -> MonoKind p
  setVarKind :: tv -> MonoKind p -> tv
  updateVarKind :: (MonoKind p -> MonoKind p) -> tv -> tv
  updateVarKindM :: Monad m => (MonoKind p -> m (MonoKind p)) -> tv -> m tv

class IsVar v => TcVar v where
  type TcDetailsThing v
  tcVarDetails :: v -> TcVarDetails (TcDetailsThing v)
  setTcVarDetails :: v -> TcVarDetails (TcDetailsThing v) -> v

{- *********************************************************************
*                                                                      *
*                   ForAllFlag
*                                                                      *
********************************************************************* -}

data ForAllFlag
  = Optional !Specificity -- type application is optional at call sight
  | Required              -- type application is required at call sight
  deriving (Eq, Ord, Data)

data Specificity = InferredSpec | SpecifiedSpec
  deriving (Eq, Ord, Data)

pattern Inferred, Specified :: ForAllFlag
pattern Inferred = Optional InferredSpec
pattern Specified = Optional SpecifiedSpec

{-# COMPLETE Required, Specified, Inferred #-}

mkForAllBinder :: vis -> v -> VarBndr v vis
mkForAllBinder vis var = Bndr var vis

mkForAllBinders :: vis -> [v] -> [VarBndr v vis]
mkForAllBinders vis = map (mkForAllBinder vis)

eqForAllVis :: ForAllFlag -> ForAllFlag -> Bool
eqForAllVis Required Required = True
eqForAllVis (Optional _) (Optional _) = True
eqForAllVis _ _ = False

isVisibleForAllFlag :: ForAllFlag -> Bool
isVisibleForAllFlag af = not (isInvisibleForAllFlag af)

isInvisibleForAllFlag :: ForAllFlag -> Bool
isInvisibleForAllFlag Optional{} = True
isInvisibleForAllFlag Required = False

instance Outputable ForAllFlag where
  ppr Required  = text "[req]"
  ppr Specified = text "[spec]"
  ppr Inferred = text "[infrd]"

instance Binary ForAllFlag where
  put_ bh Required  = putByte bh 0
  put_ bh Specified = putByte bh 1
  put_ bh Inferred = putByte bh 2

  get bh = do
    h <- getByte bh
    case h of
      0 -> return Required
      1 -> return Specified
      _ -> return Inferred

{- *********************************************************************
*                                                                      *
                   VarBndr, ForAllBinder
*                                                                      *
********************************************************************* -}

data VarBndr var argf = Bndr var argf
  deriving Data

type ForAllBinder var = VarBndr var ForAllFlag
type InvisBinder var = VarBndr var Specificity

binderVar :: VarBndr v argf -> v
binderVar (Bndr v _) = v

binderVars :: [VarBndr v argf] -> [v]
binderVars bvs = map binderVar bvs

binderFlag :: VarBndr v argf -> argf
binderFlag (Bndr _ f) = f

binderFlags :: [VarBndr v argf] -> [argf]
binderFlags bvs = map binderFlag bvs

mkVarBinder :: argf -> var -> VarBndr var argf
mkVarBinder argf var = Bndr var argf

mkVarBinders :: argf -> [var] -> [VarBndr var argf]
mkVarBinders argf = map (mkVarBinder argf)

mapVarBinder :: (v -> v') -> VarBndr v argf -> VarBndr v' argf
mapVarBinder f (Bndr v a) = Bndr (f v) a

varSpecToBinders :: [VarBndr a Specificity] -> [VarBndr a ForAllFlag]
varSpecToBinders = map varSpecToBinder

varSpecToBinder :: VarBndr a Specificity -> VarBndr a ForAllFlag
varSpecToBinder (Bndr v vis) = Bndr v (Optional vis)

instance Outputable v => Outputable (VarBndr v ForAllFlag) where
  ppr (Bndr v Required) = braces (ppr v)
  ppr (Bndr v Specified) = braces (ppr v)
  ppr (Bndr v Inferred) = braces (ppr v)

instance (Binary v, Binary f) => Binary (VarBndr v f) where
  put_ bh (Bndr v f) = do
    put_ bh v
    put_ bh f

  get bh = do
    v <- get bh
    f <- get bh
    return $ Bndr v f
