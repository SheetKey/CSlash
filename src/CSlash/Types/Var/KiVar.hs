{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Types.Var.KiVar where

import Prelude hiding ((<>))

import {-# SOURCE #-} CSlash.Core.Kind (MonoKind, FunKiFlag)
import {-# SOURCE #-} CSlash.Tc.Utils.TcType (TcVarDetails, pprTcVarDetails, vanillaSkolemVarUnk)

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
  varName (TcKiVar kv) = tc_kv_name kv
  varName kv = kv_name kv
  setVarName (TcKiVar kv) name = TcKiVar (kv { tc_kv_name = name })
  setVarName kv name = kv { kv_name = name }

  varUnique (TcKiVar kv) = tc_kv_real_unique kv
  varUnique kv = kv_real_unique kv
  setVarUnique (TcKiVar kv) u = TcKiVar (kv { tc_kv_real_unique = u })
  setVarUnique kv unique = kv { kv_real_unique = unique }

  isTcVar TcKiVar {} = True
  isTcVar _ = False

instance IsVar TcKiVar where
  varName = tc_kv_name
  setVarName kv name = kv { tc_kv_name = name }

  varUnique = tc_kv_real_unique
  setVarUnique kv unique = kv { tc_kv_real_unique = unique }

  isTcVar _ = True

instance TcVar (KiVar Tc) where
  type TcDetailsThing (KiVar Tc) = MonoKind Tc

  tcVarDetails (TcKiVar kv) = tcVarDetails kv
  tcVarDetails _ = vanillaSkolemVarUnk

instance TcVar TcKiVar where
  type TcDetailsThing TcKiVar = MonoKind Tc

  tcVarDetails = tc_kv_details

class TcKiVarMaybe v where
  toTcKiVar_maybe :: v -> Maybe TcKiVar

instance TcKiVarMaybe (KiVar p) where
  toTcKiVar_maybe (TcKiVar v) = Just v
  toTcKiVar_maybe _ = Nothing

instance TcKiVarMaybe TcKiVar where
  toTcKiVar_maybe = Just

instance Outputable (KiVar p) where
  ppr (TcKiVar kv) = ppr kv
  ppr KiVar {..} = docWithStyle ppr_code ppr_normal
    where
      ppr_code = ppr kv_name
      ppr_normal sty = getPprDebug $ \debug ->
        let ppr_var | debug = brackets $ text "kv"
                    | otherwise = empty
        in ppr kv_name <> ppr_var

instance Outputable TcKiVar where
  ppr TcKiVar' {..} = docWithStyle ppr_code ppr_normal
    where
      ppr_code = ppr tc_kv_name
      ppr_normal sty = getPprDebug $ \debug ->
        let ppr_var | dumpStyle sty || debug = brackets (pprTcVarDetails tc_kv_details)
                    | otherwise = empty
        in  ppr tc_kv_name <> ppr_var

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

instance NamedThing (KiVar p) where
  getName (TcKiVar kv) = getName kv
  getName kv = kv_name kv

instance NamedThing TcKiVar where
  getName = tc_kv_name 

instance Uniquable (KiVar p) where
  getUnique (TcKiVar kv) = getUnique kv
  getUnique kv = kv_real_unique kv

instance Uniquable TcKiVar where
  getUnique = tc_kv_real_unique

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
