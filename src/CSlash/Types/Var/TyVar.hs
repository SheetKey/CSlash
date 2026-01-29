{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module CSlash.Types.Var.TyVar where

import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import {-# SOURCE #-} CSlash.Core.Kind (MonoKind)
import {-# SOURCE #-} CSlash.Tc.Utils.TcType (TcVarDetails, pprTcVarDetails)

import CSlash.Cs.Pass

import CSlash.Types.Var.KiVar
import CSlash.Types.Var.Class

import CSlash.Types.Name hiding (varName)
import CSlash.Types.Unique

import CSlash.Utils.Binary
import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic

import Data.Data

data TyVar p where
  TyVar
    :: { tv_name :: !Name
       , tv_real_unique :: {-# UNPACK #-} !Unique
       , tv_kind :: MonoKind p -- CANNOT be Zk b/c of substitutions
       }
    -> TyVar p
  TcTyVar :: TcTyVar -> TyVar Tc

data TcTyVar = TcTyVar'
  { tc_tv_name :: !Name
  , tc_tv_real_unique :: {-# UNPACK #-} !Unique
  , tc_tv_kind :: MonoKind Tc
  , tc_tv_details :: TcVarDetails (Type Tc)
  }

instance IsVar (TyVar p) where
  varName = tv_name
  setVarName tv name = tv { tv_name = name }

  varUnique = tv_real_unique
  setVarUnique tv unique = tv { tv_real_unique = unique }

instance IsVar TcTyVar

instance TcVar (TyVar Tc) where
  type TcDetailsThing (TyVar Tc) = Type Tc

instance TcVar TcTyVar where
  type TcDetailsThing TcTyVar = Type Tc

instance Outputable (TyVar p)

instance Outputable TcTyVar

instance VarHasKind (TyVar p) p

instance VarHasKind TcTyVar Tc

instance Typeable p => Data (TyVar p) where
  toConstr _ = abstractConstr "TyVar"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "TyVar"

instance Data TcTyVar where
  toConstr _ = abstractConstr "TcTyVar"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "TcTyVar"

instance Eq (TyVar p) where
  a == b = varUnique a == varUnique b

instance Ord (TyVar p) where
  a <= b = getKey (varUnique a) <= getKey (varUnique b)
  a < b = getKey (varUnique a) < getKey (varUnique b)
  a >= b = getKey (varUnique a) >= getKey (varUnique b)
  a > b = getKey (varUnique a) > getKey (varUnique b)
  a `compare` b = varUnique a `nonDetCmpUnique` varUnique b

instance Eq TcTyVar where
  a == b = varUnique a == varUnique b

instance Ord TcTyVar where
  a <= b = getKey (varUnique a) <= getKey (varUnique b)
  a < b = getKey (varUnique a) < getKey (varUnique b)
  a >= b = getKey (varUnique a) >= getKey (varUnique b)
  a > b = getKey (varUnique a) > getKey (varUnique b)
  a `compare` b = varUnique a `nonDetCmpUnique` varUnique b

instance NamedThing (TyVar p)

instance NamedThing TcTyVar

instance Uniquable (TyVar p)

instance Uniquable TcTyVar

mkTyVar :: Name -> MonoKind p -> TyVar p
mkTyVar name kind = TyVar { tv_name = name
                          , tv_real_unique = nameUnique name
                          , tv_kind = kind }

mkTcTyVar :: Name -> MonoKind Tc -> TcVarDetails (Type Tc) -> TcTyVar
mkTcTyVar name kind details = TcTyVar' { tc_tv_name = name
                                       , tc_tv_real_unique = nameUnique name
                                       , tc_tv_kind = kind
                                       , tc_tv_details = details }

toTcTyVar_maybe :: forall p. IsPass p => TyVar (CsPass p) -> Maybe TcTyVar
toTcTyVar_maybe @p v = case csPass @p of
  Tc -> case v of
          TcTyVar v -> Just v
          _ -> Nothing
  _ -> Nothing

changeTvKind :: (MonoKind p -> MonoKind p') -> TyVar p -> TyVar p'
changeTvKind f tv = panic "changeTvKind"

{- **********************************************************************
*                                                                       *
                  PiBinder
*                                                                       *
********************************************************************** -}

data PiTyBinder p
  = NamedTy (ForAllBinder (TyVar p))
  | AnonTy (Type p)
  -- deriving Data

instance IsPass p => Outputable (PiTyBinder (CsPass p)) where
  ppr (AnonTy ty) = ppr ty
  ppr (NamedTy v) = ppr v

isInvisiblePiTyBinder :: PiTyBinder p -> Bool
isInvisiblePiTyBinder (NamedTy (Bndr _ vis)) = isInvisibleForAllFlag vis
isInvisiblePiTyBinder (AnonTy _) = True

isVisiblePiTyBinder :: PiTyBinder p -> Bool
isVisiblePiTyBinder = not . isInvisiblePiTyBinder
