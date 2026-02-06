{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module CSlash.Types.Var.TyVar where

import Prelude hiding ((<>))

import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import {-# SOURCE #-} CSlash.Core.Kind (MonoKind)
import {-# SOURCE #-} CSlash.Tc.Utils.TcType (TcVarDetails, pprTcVarDetails, vanillaSkolemVarUnk)

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
                               -- given Zk: forall (tv : k). ty
                               -- When we subst (instantiate the forall during typechecking)
                               -- we MUST subst the kind of tv
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
  varName (TcTyVar tv) = varName tv
  varName tv = tv_name tv
  setVarName (TcTyVar tv) name = TcTyVar $ setVarName tv name
  setVarName tv name = tv { tv_name = name }

  varUnique (TcTyVar tv) = varUnique tv
  varUnique tv = tv_real_unique tv
  setVarUnique (TcTyVar tv) u = TcTyVar $ setVarUnique tv u
  setVarUnique tv unique = tv { tv_real_unique = unique }

  isTcVar TcTyVar {} = True
  isTcVar _ = False

instance IsVar TcTyVar where
  varName = tc_tv_name
  setVarName tv name = tv { tc_tv_name = name }

  varUnique = tc_tv_real_unique
  setVarUnique tv unique = tv { tc_tv_real_unique = unique }

  isTcVar _ = True

instance TcVar (TyVar Tc) where
  type TcDetailsThing (TyVar Tc) = Type Tc

  tcVarDetails (TcTyVar tv) = tcVarDetails tv
  tcVarDetails _ = vanillaSkolemVarUnk

instance TcVar TcTyVar where
  type TcDetailsThing TcTyVar = Type Tc

  tcVarDetails = tc_tv_details

instance Outputable (TyVar p) where
  ppr (TcTyVar tv) = ppr tv
  ppr TyVar {..} = docWithStyle ppr_code ppr_normal
    where
      ppr_code = ppr tv_name
      ppr_normal sty = getPprDebug $ \debug ->
        let ppr_var | debug = brackets $ text "tv"
                    | otherwise = empty
        in if debug
           then parens (ppr tv_name <> ppr_var <+> colon <+> ppr tv_kind)
           else ppr tv_name <> ppr_var

instance Outputable TcTyVar where
  ppr TcTyVar' {..} = docWithStyle ppr_code ppr_normal
    where
      ppr_code = ppr tc_tv_name
      ppr_normal sty = getPprDebug $ \debug ->
        let ppr_var | dumpStyle sty || debug = brackets (pprTcVarDetails tc_tv_details)
                    | otherwise = empty
        in if debug
           then parens (ppr tc_tv_name <> ppr_var <+> colon <+> ppr tc_tv_kind)
           else ppr tc_tv_name <> ppr_var

instance VarHasKind (TyVar p) p where
  varKind (TcTyVar tv) = varKind tv
  varKind TyVar {..} = tv_kind

  setVarKind (TcTyVar tv) k = TcTyVar $ setVarKind tv k
  setVarKind tv k = tv { tv_kind = k }

  updateVarKind f (TcTyVar tv) = TcTyVar $ updateVarKind f tv
  updateVarKind f (TyVar { tv_kind = ki, .. }) = TyVar { tv_kind = f ki, .. }

  updateVarKindM f (TcTyVar tv) = TcTyVar <$> updateVarKindM f tv
  updateVarKindM f (TyVar { tv_kind = ki, .. }) = do
    ki' <- f ki
    return $ TyVar { tv_kind = ki', .. }

instance VarHasKind TcTyVar Tc where
  varKind = tc_tv_kind
  setVarKind tv ki = tv { tc_tv_kind = ki }
  updateVarKind f (TcTyVar' { tc_tv_kind = ki, .. }) = TcTyVar' { tc_tv_kind = f ki, .. }
  updateVarKindM f (TcTyVar' { tc_tv_kind = ki, .. }) = do
    ki' <- f ki
    return $ TcTyVar' { tc_tv_kind = ki', .. }

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

instance NamedThing (TyVar p) where
  getName (TcTyVar tv) = getName tv
  getName tv = tv_name tv

instance NamedThing TcTyVar where
  getName = tc_tv_name 

instance Uniquable (TyVar p) where
  getUnique (TcTyVar tv) = getUnique tv
  getUnique tv = tv_real_unique tv

instance Uniquable TcTyVar where
  getUnique = tc_tv_real_unique

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
