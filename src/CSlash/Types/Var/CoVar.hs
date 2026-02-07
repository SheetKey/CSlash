{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module CSlash.Types.Var.CoVar where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import {-# SOURCE #-} CSlash.Core.Kind (MonoKind)
import {-# SOURCE #-} CSlash.Tc.Utils.TcType (TcVarDetails, pprTcVarDetails, vanillaSkolemVarUnk)

import CSlash.Types.Var.Class

import CSlash.Types.Name hiding (varName)
import CSlash.Types.Unique

import CSlash.Utils.Misc
import CSlash.Utils.Outputable

import Data.Data
import Data.Void

data CoVar thing p where
  CoVar
    :: { cv_name :: !Name
       , cv_real_unique :: {-# UNPACK #-} !Unique
       , cv_thing :: thing p
       }
    -> CoVar thing p
  TcCoVar :: (TcCoVar MonoKind) -> CoVar MonoKind Tc -- no TcCoVars for TyCoVars (yet)
             -- if they are needed, replace MonoKind with thing
             -- also, TcCoVar must accept another argument for the coercion type

data TcCoVar thing = TcCoVar'
  { tc_cv_name :: !Name
  , tc_cv_real_unique :: {-# UNPACK #-} !Unique
  , tc_cv_thing :: thing Tc
  , tc_cv_details :: TcVarDetails Void -- No MetaCoVars, use HoleCoercion instead
  } 

type KiCoVar = CoVar MonoKind
type TcKiCoVar = TcCoVar MonoKind

type TyCoVar = CoVar Type
type TcTyCoVar = TcCoVar Type

instance VarHasType (TyCoVar p) p

instance VarHasType TcTyCoVar Tc

instance VarHasKind (KiCoVar p) p where
  varKind (TcCoVar cv) = tc_cv_thing cv
  varKind cv = cv_thing cv

  setVarKind (TcCoVar cv) ki = TcCoVar $ setVarKind cv ki
  setVarKind kcv ki = kcv { cv_thing = ki }

  updateVarKind f (TcCoVar cv) = TcCoVar $ updateVarKind f cv
  updateVarKind f (CoVar {..}) = CoVar { cv_thing = f cv_thing, .. }

  updateVarKindM f (TcCoVar cv) = TcCoVar <$> updateVarKindM f cv
  updateVarKindM f (CoVar {..}) = do
    ki' <- f cv_thing
    return $ CoVar { cv_thing = ki', .. }

instance VarHasKind TcKiCoVar Tc where
  varKind = tc_cv_thing

  setVarKind cv ki = cv { tc_cv_thing = ki }

  updateVarKind f (TcCoVar' {..}) = TcCoVar' { tc_cv_thing = f tc_cv_thing, .. }

  updateVarKindM f (TcCoVar' {..}) = do
    ki' <- f tc_cv_thing
    return $ TcCoVar' { tc_cv_thing = ki', .. }

instance Outputable (thing p) => IsVar (CoVar thing p) where
  isTcVar TcCoVar {} = True
  isTcVar _ = False

  varName (TcCoVar cv) = tc_cv_name cv
  varName cv = cv_name cv

  setVarName (TcCoVar cv) nm = TcCoVar $ cv { tc_cv_name = nm }
  setVarName cv nm = cv { cv_name = nm }

  varUnique (TcCoVar cv) = tc_cv_real_unique cv
  varUnique cv = cv_real_unique cv

  setVarUnique (TcCoVar cv) u = TcCoVar $ cv { tc_cv_real_unique = u }
  setVarUnique cv u = cv { cv_real_unique = u }

instance IsVar TcTyCoVar where
  isTcVar _ = True
  varName = tc_cv_name
  setVarName cv nm = cv { tc_cv_name = nm }
  varUnique = tc_cv_real_unique
  setVarUnique cv u = cv { tc_cv_real_unique = u }

instance IsVar TcKiCoVar where
  isTcVar _ = True
  varName = tc_cv_name
  setVarName cv nm = cv { tc_cv_name = nm }
  varUnique = tc_cv_real_unique
  setVarUnique cv u = cv { tc_cv_real_unique = u }

instance (Typeable thing, Typeable p) => Data (CoVar thing p) where
  toConstr _ = abstractConstr "CoVar"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "CoVar"

instance TcVar (KiCoVar Tc) where
  type TcDetailsThing (KiCoVar Tc) = Void

  tcVarDetails (TcCoVar tv) = tcVarDetails tv
  tcVarDetails _ = vanillaSkolemVarUnk

instance TcVar TcKiCoVar where
  type TcDetailsThing TcKiCoVar = Void

  tcVarDetails = tc_cv_details

instance Outputable (thing p) => Outputable (CoVar thing p) where
  ppr (TcCoVar cv) = ppr cv
  ppr CoVar {..} = docWithStyle ppr_code ppr_normal
    where
      ppr_code = ppr cv_name
      ppr_normal sty = getPprDebug $ \debug ->
        let ppr_var | debug = brackets (text "CoVarId")
                    | otherwise = empty
        in if debug
           then parens (ppr cv_name <+> ppr_var <+> colon <+> ppr cv_thing)
           else ppr cv_name <> ppr_var        

instance Outputable (thing Tc) => Outputable (TcCoVar thing) where
  ppr TcCoVar' {..} = docWithStyle ppr_code ppr_normal
    where
      ppr_code = ppr tc_cv_name
      ppr_normal sty = getPprDebug $ \debug ->
        let ppr_var | dumpStyle sty || debug = brackets (pprTcVarDetails tc_cv_details)
                    | otherwise = empty
        in if debug
           then parens (ppr tc_cv_name <> ppr_var <+> colon <+> ppr tc_cv_thing)
           else ppr tc_cv_name <> ppr_var

instance NamedThing (CoVar thing p) where
  getName (TcCoVar cv) = tc_cv_name cv
  getName cv = cv_name cv

instance NamedThing (TcCoVar thing) where
  getName = tc_cv_name

instance Uniquable (CoVar thing p) where
  getUnique (TcCoVar cv) = tc_cv_real_unique cv
  getUnique cv = cv_real_unique cv

instance Uniquable (TcCoVar thing) where
  getUnique = tc_cv_real_unique

instance Eq (CoVar thing p) where
  a == b = getUnique a == getUnique b

instance Eq (TcCoVar thing) where
  a == b = getUnique a == getUnique b

instance Ord (CoVar thing p) where
  a <= b = getKey (getUnique a) <= getKey (getUnique b)
  a < b = getKey (getUnique a) < getKey (getUnique b)
  a >= b = getKey (getUnique a) >= getKey (getUnique b)
  a > b = getKey (getUnique a) > getKey (getUnique b)
  a `compare` b = getUnique a `nonDetCmpUnique` getUnique b

instance Ord (TcCoVar thing) where
  a <= b = getKey (getUnique a) <= getKey (getUnique b)
  a < b = getKey (getUnique a) < getKey (getUnique b)
  a >= b = getKey (getUnique a) >= getKey (getUnique b)
  a > b = getKey (getUnique a) > getKey (getUnique b)
  a `compare` b = getUnique a `nonDetCmpUnique` getUnique b

mkCoVar :: Name -> thing p -> CoVar thing p
mkCoVar name thing = CoVar { cv_name = name
                           , cv_real_unique = nameUnique name
                           , cv_thing = thing }

mkTcKiCoVar :: Name -> MonoKind Tc -> TcVarDetails Void -> TcKiCoVar
mkTcKiCoVar name kind details = TcCoVar' { tc_cv_name = name
                                         , tc_cv_real_unique = nameUnique name
                                         , tc_cv_thing = kind
                                         , tc_cv_details = details }

changeCvTypeM :: Monad m => (Type p -> m (Type p')) -> TyCoVar p -> m (TyCoVar p')
changeCvTypeM f (CoVar name uniq thing) = (CoVar name uniq) <$> f thing
