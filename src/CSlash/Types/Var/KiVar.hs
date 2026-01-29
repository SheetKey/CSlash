{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Types.Var.KiVar where

import {-# SOURCE #-} CSlash.Core.Kind (MonoKind, FunKiFlag)
import {-# SOURCE #-} CSlash.Tc.Utils.TcType (TcVarDetails, pprTcVarDetails)

import CSlash.Cs.Pass

import CSlash.Types.Var.Class

import CSlash.Types.Name hiding (varName)
import CSlash.Types.Unique

import CSlash.Utils.Binary
import CSlash.Utils.Outputable
import CSlash.Utils.Misc

import Data.Data

data KiVar p where
  KiVar
    :: { kv_name :: !Name
       , kv_real_unique :: {-# UNPACK #-} !Unique
       }
    -> KiVar p
  TcKiVar :: TcKiVar -> KiVar Tc

data TcKiVar = TcKiVar'
  { tc_kv_name :: !Name
  , tc_kv_real_unique :: {-# UNPACK #-} !Unique
  , tc_kv_details :: TcVarDetails (MonoKind Tc)
  }

instance IsVar (KiVar p) where
  varName = kv_name
  setVarName kv name = kv { kv_name = name }

  varUnique = kv_real_unique
  setVarUnique kv unique = kv { kv_real_unique = unique }

instance IsVar TcKiVar where
  varName = tc_kv_name
  setVarName kv name = kv { tc_kv_name = name }

  varUnique = tc_kv_real_unique
  setVarUnique kv unique = kv { tc_kv_real_unique = unique }

instance TcVar (KiVar Tc) where
  type TcDetailsThing (KiVar Tc) = MonoKind Tc

instance TcVar TcKiVar where
  type TcDetailsThing TcKiVar = MonoKind Tc

class TcKiVarMaybe v where
  toTcKiVar_maybe :: v -> Maybe TcKiVar

instance TcKiVarMaybe (KiVar p)

instance TcKiVarMaybe TcKiVar

instance Outputable (KiVar p)

instance Outputable TcKiVar

instance Typeable p => Data (KiVar p) where
  toConstr _ = abstractConstr "KiVar"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "KiVar"

instance Data TcKiVar where
  toConstr _ = abstractConstr "TcKiVar"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "TcKiVar"

instance Eq (KiVar p) where
  a == b = varUnique a == varUnique b

instance Ord (KiVar p) where
  a <= b = getKey (varUnique a) <= getKey (varUnique b)
  a < b = getKey (varUnique a) < getKey (varUnique b)
  a >= b = getKey (varUnique a) >= getKey (varUnique b)
  a > b = getKey (varUnique a) > getKey (varUnique b)
  a `compare` b = varUnique a `nonDetCmpUnique` varUnique b

instance Eq TcKiVar where
  a == b = varUnique a == varUnique b

instance Ord TcKiVar where
  a <= b = getKey (varUnique a) <= getKey (varUnique b)
  a < b = getKey (varUnique a) < getKey (varUnique b)
  a >= b = getKey (varUnique a) >= getKey (varUnique b)
  a > b = getKey (varUnique a) > getKey (varUnique b)
  a `compare` b = varUnique a `nonDetCmpUnique` varUnique b

instance NamedThing (KiVar p)

instance NamedThing TcKiVar

instance Uniquable (KiVar p)

instance Uniquable TcKiVar

mkKiVar :: Name -> KiVar p
mkKiVar name = KiVar { kv_name = name
                     , kv_real_unique = nameUnique name }

mkTcKiVar :: Name -> TcVarDetails (MonoKind Tc) -> TcKiVar
mkTcKiVar name details = TcKiVar' { tc_kv_name = name
                                  , tc_kv_real_unique = nameUnique name
                                  , tc_kv_details = details }

{- **********************************************************************
*                                                                       *
                  PiBinder
*                                                                       *
********************************************************************** -}

data PiKiBinder p
  = Named (KiVar p)
  | Anon (MonoKind p) FunKiFlag
  deriving Data

instance Outputable (PiKiBinder p) where
  ppr (Anon ki af) = ppr af <+> ppr ki
  ppr (Named v) = ppr v

namedPiKiBinder_maybe :: PiKiBinder p -> Maybe (KiVar p)
namedPiKiBinder_maybe (Named kv) = Just kv
namedPiKiBinder_maybe _ = Nothing
