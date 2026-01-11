{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiWayIf #-}

module CSlash.Types.Var
  ( {-* Var *-}
    Var

    {-* Class methods *-}
  , IsVar
  , VarHasName(..), VarHasUnique(..)
  , VarHasType(..), VarHasKind(..), ChangeVarKind(..)
  , TcVar(..)
  , IsTyVar(..), IsKiVar(..)
  -- , VarHasTcDetails(..), VarCanSetTcDetails(..)
  , ToVar(..), ToAnyTyVar(..), ToAnyKiVar(..)
  , ToTcTyVarMaybe(..), ToAnyTyVarMaybe(..)
  , ToKiVarMaybe(..), ToTcKiVarMaybe(..), ToAnyKiVarMaybe(..)
  , ToIdMaybe(..)
  , FromTyVar(..), FromTcTyVar(..), FromAnyTyVar(..)
  , FromKiVar(..), FromTcKiVar(..), FromAnyKiVar(..)
  , FromId(..)
  , AsAnyTy(..), AsAnyKi(..)
  , AsGenericTy(..), AsGenericKi(..)

    {-* TyVar *-}
  , TyVar, KiCoVar
  , mkTyVar, toKiCoVar_maybe, mkLocalKiCoVar
  , isKiCoVar

    {-* TcTyVar *-}
  , TcTyVar
  , mkTcTyVar

    {-* AnyTyVar *-}
  , AnyTyVar
  , handleAnyTv

    {-* KiVar *-}
  , KiVar
  , mkKiVar

    {-* TcKiVar *-}
  , TcKiVar
  , mkTcKiVar
  
    {-* AnyKiVar *-}
  , AnyKiVar
  , handleAnyKv, handleTcKv
  , filterAnyTcKiVar, filterTcKiVar

    {-* Id *-}
  , Id, TyCoVar
  , mkGlobalVar, mkLocalVar
  , idInfo, idDetails
  , isGlobalId, isExportedId, isLocalId
  , updateIdTypeM
  , changeIdTypeM

    {-* ForAllFlag *-}
  , ForAllFlag(Optional, Required, Specified, Inferred)
  , Specificity(..)
  , isVisibleForAllFlag, isInvisibleForAllFlag
  , eqForAllVis
  , mkForAllBinder, mkForAllBinders
  , varSpecToBinder, varSpecToBinders
  
    {-* VarBndr *-}
  , VarBndr(..), ForAllBinder, InvisBinder, TyVarBinder
  , binderVar, binderVars
  , binderFlag, binderFlags
  , mkVarBinder, mkVarBinders
  , mapVarBinder

    {-* PiKiBinder *-}
  , PiKiBinder(..)
  , namedPiKiBinder_maybe

    {-* PiTyBinder *-}
  , PiTyBinder(..)
  , isVisiblePiTyBinder, isInvisiblePiTyBinder
  ) where

import Prelude hiding ((<>))

import {-# SOURCE #-} CSlash.Core.Type.Rep (Type, PredType)
import {-# SOURCE #-} CSlash.Core.Type.Ppr (pprType)
import {-# SOURCE #-} CSlash.Core.Kind
  (Kind, MonoKind, PredKind, FunKiFlag, pprKind, isKiCoVarKind)
import {-# SOURCE #-} CSlash.Tc.Utils.TcType
  ( TcVarDetails, pprTcVarDetails )
import {-# SOURCE #-} CSlash.Types.Id.Info (IdDetails, IdInfo, pprIdDetails)

import CSlash.Types.Name hiding (varName)
import CSlash.Types.Unique ( Uniquable, Unique, getKey, getUnique, nonDetCmpUnique )

import CSlash.Utils.Misc
import CSlash.Utils.Binary
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import CSlash.Data.FastString

import Data.Data
import Control.DeepSeq
import Data.Void (Void, absurd)
import Data.Bifunctor(Bifunctor(..))

{- *********************************************************************
*                                                                      *
                    Var
*                                                                      *
********************************************************************* -}

data Var tv kv
  = TyVar'
    { _varName :: !Name
    , _realUnique :: {-# UNPACK #-} !Unique
    , _varKind :: MonoKind kv
    }
  | TcTyVar' -- for type inference
    { _varName :: !Name
    , _realUnique :: {-# UNPACK #-} !Unique
    , _varKind :: MonoKind kv
    , _tc_tv_details :: TcVarDetails (Type (AnyTyVar AnyKiVar) AnyKiVar)
    }
  | KiVar'
    { _varName :: !Name
    , _realUnique :: {-# UNPACK #-} !Unique
    }
  | TcKiVar' -- for kind inference
    { _varName :: !Name
    , _realUnique :: {-# UNPACK #-} !Unique
    , _tc_kv_details :: TcVarDetails (MonoKind AnyKiVar)
    }
  | Id'
    { _varName :: !Name
    , _realUnique :: {-# UNPACK #-} !Unique
    , _varType :: Type tv kv
    , _idScope :: IdScope
    , _id_details :: IdDetails tv kv
    , _id_info :: IdInfo
    }

instance Functor (Var tv) where
  fmap = panic "instance Functor (Var tv)"

instance Bifunctor Var where
  bimap _ _ (KiVar' {..}) = KiVar' {..}
  bimap _ _ (TcKiVar' {..}) = TcKiVar' {..}
  bimap _ _ _ = panic "instance Bifunctor Var"

  first _ (TyVar' {..}) = TyVar' {..}
  first _ (TcTyVar' {..}) = TcTyVar' {..}
  first _ (KiVar' {..}) = KiVar' {..}
  first _ (TcKiVar' {..}) = TcKiVar' {..}
  first _ _ = panic "instance Bifunctor Var"

  second _ (KiVar' {..}) = KiVar' {..}
  second _ (TcKiVar' {..}) = TcKiVar' {..}
  second _ _ = panic "instance Bifunctor Var"

vacuousBimap :: Var Void Void -> Var tv kv
vacuousBimap = bimap absurd absurd

vacuousBimap' ::Var tv kv -> Var Void Void
vacuousBimap' = bimap undefined undefined

vacuousFirst :: Var Void kv -> Var tv kv
vacuousFirst = first absurd

vacuousFirst' :: Var tv kv -> Var Void kv
vacuousFirst' = first undefined

data IdScope
  = GlobalId
  | LocalId ExportFlag

data ExportFlag
  = NotExported
  | Exported

instance {-# OVERLAPPING #-} Outputable kv => Outputable (Var Void kv) where
  ppr var = 
    getPprDebug $ \ debug ->
    getPprStyle $ \ sty ->
    let ppr_var = case var of
          (TyVar' {}) | debug -> brackets (text "tv")
          (KiVar' {}) | debug -> brackets (text "kv")
          (TcTyVar' { _tc_tv_details = d })
            | dumpStyle sty || debug
            -> brackets (pprTcVarDetails d)
          (TcKiVar' { _tc_kv_details = d })
            | dumpStyle sty || debug
            -> brackets (pprTcVarDetails d)
          _ -> empty
        ppr_tyki = case var of
          (TyVar' { _varKind = ki }) -> char ' ' <> colon <+> ppr ki
          (TcTyVar' { _varKind = ki }) -> char ' ' <> colon <+> ppr ki
          _ -> empty

    in if debug
       then parens (ppr (_varName var) <+> ppr_var <> ppr_tyki)
       else ppr (_varName var) <> ppr_var
    
instance IsTyVar tv kv => Outputable (Var tv kv) where
  ppr var = 
    getPprDebug $ \ debug ->
    getPprStyle $ \ sty ->
    let ppr_var = case var of
          (TyVar' {}) | debug -> brackets (text "tv")
          (KiVar' {}) | debug -> brackets (text "kv")
          (TcTyVar' { _tc_tv_details = d })
            | dumpStyle sty || debug
            -> brackets (pprTcVarDetails d)
          (TcKiVar' { _tc_kv_details = d })
            | dumpStyle sty || debug
            -> brackets (pprTcVarDetails d)
          (Id' { _idScope = s, _id_details = d })
            | debug
            -> brackets (ppr_id_scope s <> pprIdDetails d)
          _ -> empty
        ppr_tyki = case var of
          (TyVar' { _varKind = ki }) -> char ' ' <> colon <+> ppr ki
          (TcTyVar' { _varKind = ki }) -> char ' ' <> colon <+> ppr ki
          (Id' { _varType = ty }) -> char ' ' <> colon <+> pprType ty
          _ -> empty
          
    in if debug
       then parens (ppr (_varName var) <+> ppr_var <> ppr_tyki)
       else ppr (_varName var) <> ppr_var
    
ppr_id_scope :: IdScope -> SDoc
ppr_id_scope GlobalId = text "gid"
ppr_id_scope (LocalId Exported) = text "lidx"
ppr_id_scope (LocalId NotExported) = text "lid"

instance NamedThing (Var tv kv) where
  getName = varName

instance Uniquable (Var tv kv) where
  getUnique = _realUnique

instance Eq (Var tv kv) where
  a == b = _realUnique a == _realUnique b

instance Ord (Var tv kv) where
  a <= b = getKey (_realUnique a) <= getKey (_realUnique b)
  a < b = getKey (_realUnique a) < getKey (_realUnique b)
  a >= b = getKey (_realUnique a) >= getKey (_realUnique b)
  a > b = getKey (_realUnique a) > getKey (_realUnique b)
  a `compare` b = a `nonDetCmpVar` b
    where
      -- nonDetCmpVar :: Var -> Var -> Ordering
      nonDetCmpVar a b = _realUnique a `nonDetCmpUnique` _realUnique b

instance (Typeable tv, Typeable kv) => Data (Var tv kv) where
  toConstr _ = abstractConstr "Var"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "Var"

instance HasOccName (Var tv kv) where
  occName = nameOccName . varName

{- *********************************************************************
*                                                                      *
                    Utility classes
*                                                                      *
********************************************************************* -}

type IsVar v = (Eq v, Ord v, Outputable v, VarHasName v, VarHasUnique v)

class NamedThing v => VarHasName v where
  varName :: v -> Name
  setVarName :: v -> Name -> v

instance VarHasName (Var tv kv) where
  varName = _varName
  setVarName var new_name = var { _realUnique = getUnique new_name
                                , _varName = new_name }

class Uniquable v => VarHasUnique v where
  varUnique :: v -> Unique
  setVarUnique :: v -> Unique -> v

instance VarHasUnique (Var tv kv) where
  varUnique = _realUnique
  setVarUnique var uniq = var { _realUnique = uniq
                              , _varName = setNameUnique (_varName var) uniq }

class VarHasType v tv kv | v -> tv, v -> kv where
  varType :: v -> Type tv kv
  updateVarType :: (Type tv kv -> Type tv kv) -> v -> v
  setVarType :: v -> Type tv kv -> v

class (IsVar v, IsVar kv) => VarHasKind v kv | v -> kv where
  varKind :: v -> MonoKind kv
  -- updateVarKind :: (MonoKind kv -> MonoKind kv) -> v -> v
  -- updateVarKindM :: Monad m => (MonoKind kv -> m (MonoKind kv)) -> v -> m v
  setVarKind :: v -> (MonoKind kv) -> v
  toTyVar_maybe :: v -> Maybe (TyVar kv)
  updateVarKind :: (MonoKind kv -> MonoKind kv) -> v -> v
  updateVarKindM :: Monad m => (MonoKind kv -> m (MonoKind kv)) -> v -> m v

class ChangeVarKind v where
  changeVarKind :: Outputable kv => (MonoKind kv -> MonoKind kv') -> v kv -> v kv'
  changeVarKindM :: (Monad m, Outputable kv)
                 => (MonoKind kv -> m (MonoKind kv')) -> v kv -> m (v kv')

class IsVar v => TcVar v where
  type TcDetailsThing v
  tcVarDetails :: v -> TcVarDetails (TcDetailsThing v)
  setTcVarDetails :: v -> TcVarDetails (TcDetailsThing v) -> v

-- class VarHasTcDetails v tk where
--   tcVarDetails :: v -> TcVarDetails tk

-- class VarCanSetTcDetails v tk where
--   setTcVarDetails :: v -> TcVarDetails tk -> v

class ToAnyKiVar v => IsKiVar v where
  mkKiVar :: Name -> v  
  toGenericKiVar :: KiVar -> v

class (IsKiVar kv, VarHasKind tv kv, ToAnyTyVar tv kv) => IsTyVar tv kv | tv -> kv where
  mkTyVar :: Name -> MonoKind kv -> tv
  toGenericTyVar :: TyVar kv -> tv

class (IsVar v, IsVar kv) => ToTcTyVarMaybe v kv | v -> kv where
  toTcTyVar_maybe :: v -> Maybe (TcTyVar kv)

instance IsTyVar tv kv => ToTcTyVarMaybe (Var tv kv) kv where
  toTcTyVar_maybe tv@(TcTyVar' {}) = Just $ TcTyVar $ vacuousFirst' tv
  toTcTyVar_maybe _ = Nothing

class ToAnyTyVarMaybe v kv | v -> kv where
  toAnyTyVar_maybe :: v -> Maybe (AnyTyVar kv)

instance ToAnyTyVarMaybe (Var tv kv) kv where
  toAnyTyVar_maybe tv@(TyVar' {}) = Just $ AnyTyVar $ vacuousFirst' tv
  toAnyTyVar_maybe tv@(TcTyVar' {}) = Just $ AnyTyVar $ vacuousFirst' tv
  toAnyTyVar_maybe _ = Nothing

class ToKiVarMaybe v where
  toKiVar_maybe :: v -> Maybe KiVar

instance ToKiVarMaybe (Var tv kv) where
  toKiVar_maybe kv@(KiVar' {}) = Just $ KiVar $ vacuousBimap' kv
  toKiVar_maybe _ = Nothing

class IsVar v => ToTcKiVarMaybe v where
  toTcKiVar_maybe :: v -> Maybe TcKiVar

-- instance VarHasKind tv kv => ToTcKiVarMaybe (Var tv kv) where
--   toTcKiVar_maybe kv@(TcKiVar' {}) = Just $ TcKiVar $ vacuousBimap' kv
--   toTcKiVar_maybe _ = Nothing

class ToAnyKiVarMaybe v where
  toAnyKiVar_maybe :: v -> Maybe AnyKiVar

instance ToAnyKiVarMaybe (Var tv kv) where
  toAnyKiVar_maybe kv@(KiVar' {}) = Just $ AnyKiVar $ vacuousBimap' kv
  toAnyKiVar_maybe kv@(TcKiVar' {}) = Just $ AnyKiVar $ vacuousBimap' kv
  toAnyKiVar_maybe _ = Nothing

class ToIdMaybe v tv kv | v -> tv, v -> kv where
  toId_maybe :: v -> Maybe (Id tv kv)

instance ToIdMaybe (Var tv kv) tv kv where
  toId_maybe id@(Id' {}) = Just $ Id id
  toId_maybe _ = Nothing

class ToVar v tv kv | v -> tv, v -> kv where
  toVar :: v -> Var tv kv

class ToAnyTyVar v kv | v -> kv where
  toAnyTyVar :: v -> AnyTyVar kv

class IsVar v => ToAnyKiVar v where
  toAnyKiVar :: v -> AnyKiVar

class FromTyVar v kv | v -> kv where
  fromTv :: TyVar kv -> v

instance FromTyVar (Var tv kv) kv where
  fromTv (TyVar tv) = vacuousFirst tv

class FromTcTyVar v kv | v -> kv where
  fromTcTv :: TcTyVar kv -> v

instance FromTcTyVar (Var tv kv) kv where
  fromTcTv (TcTyVar tv) = vacuousFirst tv

class FromAnyTyVar v kv | v -> kv where
  fromAnyTyVar :: AnyTyVar kv -> v

instance FromAnyTyVar (Var tv kv) kv where
  fromAnyTyVar (AnyTyVar tv) = vacuousFirst tv

class FromKiVar v where
  fromKv :: KiVar -> v

instance FromKiVar (Var tv kv) where
  fromKv (KiVar kv) = vacuousBimap kv

class FromTcKiVar v where
  fromTcKv :: TcKiVar -> v

instance FromTcKiVar (Var tv kv) where
  fromTcKv (TcKiVar kv) = vacuousBimap kv

class FromAnyKiVar v where
  fromAnyKiVar :: AnyKiVar -> v

instance FromAnyKiVar (Var tv kv) where
  fromAnyKiVar (AnyKiVar kv) = vacuousBimap kv

class FromId v tv kv | v -> tv, v -> kv where
  fromId :: Id tv kv -> v

class AsAnyTy thing where
  asAnyTy :: ToAnyTyVar tv kv => thing tv kv -> thing (AnyTyVar kv) kv
  asAnyTyKi :: (ToAnyTyVar tv kv, ToAnyKiVar kv)
            => thing tv kv -> thing (AnyTyVar AnyKiVar) AnyKiVar

class AsAnyKi thing where
  asAnyKi :: ToAnyKiVar kv => thing kv -> thing AnyKiVar

class AsGenericTy thing where
  asGenericTyKi :: IsTyVar tv kv => thing (TyVar KiVar) KiVar -> thing tv kv

class AsGenericKi thing where
  asGenericKi :: IsKiVar kv => thing KiVar -> thing kv

instance AsGenericKi TyVar where
  asGenericKi (TyVar (TyVar' { _varKind = kind, .. }))
    = TyVar $ TyVar' { _varKind = asGenericKi kind, .. }
  asGenericKi other = panic "AsGenericKi TyVar other"
                      
instance AsGenericKi AnyTyVar where
  asGenericKi (AnyTyVar (TyVar' { _varKind = kind, .. }))
    = AnyTyVar $ TyVar' { _varKind = asGenericKi kind, .. }
  asGenericKi (AnyTyVar (TcTyVar' { _varKind = kind, .. }))
    = AnyTyVar $ TcTyVar' { _varKind = asGenericKi kind, .. }
  asGenericKi other = panic "AsGenericKi TyVar other"

instance AsAnyTy Id where
  asAnyTyKi (Id (Id' {..})) = Id $ Id'
    { _varType = asAnyTyKi _varType, _id_details = asAnyTyKi _id_details, .. }
  asAnyTyKi _ = panic "AsAnyTy Id"

instance AsAnyKi TyVar where
  asAnyKi (TyVar (TyVar' {..})) = TyVar $ TyVar' { _varKind = asAnyKi _varKind, .. }
  asAnyKi _ = panic "AsAnyKi TyVar"

instance AsAnyKi TcTyVar where
  asAnyKi (TcTyVar (TcTyVar' {..})) = TcTyVar $ TcTyVar' { _varKind = asAnyKi _varKind, .. }
  asAnyKi _ = panic "AsAnyKi TcTyVar"

instance AsAnyKi AnyTyVar where
  asAnyKi (AnyTyVar (TyVar' {..})) = AnyTyVar $ TyVar' { _varKind = asAnyKi _varKind, .. }
  asAnyKi (AnyTyVar (TcTyVar' {..})) = AnyTyVar $ TcTyVar' { _varKind = asAnyKi _varKind, .. }
  asAnyKi _ = panic "AsAnyKi AnyTyVar"

{- *********************************************************************
*                                                                      *
                    TyVar
*                                                                      *
********************************************************************* -}

newtype TyVar kv = TyVar (Var Void kv)
  deriving ( Outputable, NamedThing, Uniquable, Eq, Ord, Data, HasOccName
           , VarHasName, VarHasUnique)

type KiCoVar = TyVar

toKiCoVar_maybe :: VarHasKind tv kv => tv -> Maybe (KiCoVar kv)
toKiCoVar_maybe mtv
  | Just tv <- toTyVar_maybe mtv
  , isKiCoVarKind (varKind tv)
  = Just tv
  | otherwise
  = Nothing

isKiCoVar :: VarHasKind tv kv => tv -> Bool
isKiCoVar = isKiCoVarKind . varKind

mkLocalKiCoVar :: Name -> PredKind AnyKiVar -> KiCoVar AnyKiVar
mkLocalKiCoVar name ki = assert (isKiCoVarKind ki) $ mkTyVar name ki

instance ToAnyTyVar (TyVar kv) kv where
  toAnyTyVar (TyVar tv) = AnyTyVar tv

instance IsVar kv => VarHasKind (TyVar kv) kv where
  varKind (TyVar (TyVar' { _varKind = ki })) = ki
  varKind other = pprPanic "Bad TyVar" (ppr other)

  updateVarKind upd (TyVar var@(TyVar' {})) = TyVar (var { _varKind = upd (_varKind var) })
  updateVarKind _ other = pprPanic "Bad TyVar" (ppr other)

  updateVarKindM upd (TyVar var) = do
    kind <- upd (_varKind var)
    return $ TyVar (var { _varKind = kind })

  setVarKind (TyVar tv) k = TyVar (tv { _varKind = k })

instance ChangeVarKind TyVar where
  changeVarKind upd (TyVar (TyVar' {..})) = TyVar $ TyVar' { _varKind = upd _varKind, .. }
  changeVarKind _ other = pprPanic "Bad TyVar" (ppr other)
  
  changeVarKindM upd (TyVar (TyVar' {..})) = do
    kind <- upd _varKind
    return $ TyVar $ TyVar' { _varKind = kind, .. }
  changeVarKindM _ other = pprPanic "Bad TyVar" (ppr other)

instance IsKiVar kv => IsTyVar (TyVar kv) kv where
  mkTyVar name kind = TyVar (TyVar' { _varName = name
                                    , _realUnique = nameUnique name
                                    , _varKind = kind })
  toGenericTyVar var = var

{- *********************************************************************
*                                                                      *
                    TcyTyVar
*                                                                      *
********************************************************************* -}

newtype TcTyVar kv = TcTyVar (Var Void kv)
  deriving ( Outputable, NamedThing, Uniquable, Eq, Ord, Data, HasOccName
           , VarHasName, VarHasUnique)
  
instance ToAnyTyVar (TcTyVar kv) kv where
  toAnyTyVar (TcTyVar tv) = AnyTyVar tv

instance IsVar kv => VarHasKind (TcTyVar kv) kv where
  varKind (TcTyVar (TcTyVar' { _varKind = ki })) = ki
  varKind other = pprPanic "Bad TcTyVar" (ppr other)

  updateVarKind upd (TcTyVar var@(TcTyVar' {}))
    = TcTyVar (var { _varKind = upd (_varKind var) })
  updateVarKind _ other = pprPanic "Bad TcTyVar" (ppr other)

  updateVarKindM upd (TcTyVar var) = do
    kind <- upd (_varKind var)
    return $ TcTyVar (var { _varKind = kind })

  setVarKind (TcTyVar tv) k = TcTyVar (tv { _varKind = k })

instance ChangeVarKind TcTyVar where
  changeVarKind upd (TcTyVar (TcTyVar' {..}))
    = TcTyVar $ TcTyVar' { _varKind = upd _varKind, .. }
  changeVarKind _ other = pprPanic "Bad TcTyVar" (ppr other)

  changeVarKindM upd (TcTyVar (TcTyVar' {..})) = do
    kind <- upd _varKind
    return $ TcTyVar $ TcTyVar' { _varKind = kind, .. }
  changeVarKindM _ other = pprPanic "Bad TcTyVar" (ppr other)

instance Outputable kv => TcVar (TcTyVar kv) where
  type TcDetailsThing (TcTyVar kv) = Type (AnyTyVar AnyKiVar) AnyKiVar

  tcVarDetails (TcTyVar (TcTyVar' { _tc_tv_details = details })) = details
  tcVarDetails other = pprPanic "Bad TcKiVar" (ppr other)

  setTcVarDetails (TcTyVar v) d = TcTyVar (v { _tc_tv_details = d })

-- instance Outputable kv => VarHasTcDetails (TcTyVar kv) (Type (TcTyVar kv) kv) where
--   tcVarDetails (TcTyVar (TcTyVar' { _tc_tv_details = details })) = details
--   tcVarDetails other = pprPanic "Bad TcKiVar" (ppr other)

-- instance VarCanSetTcDetails (TcTyVar kv) (Type (TcTyVar kv) kv) where
--   setTcVarDetails (TcTyVar v) d = TcTyVar (v { _tc_tv_details = d })

mkTcTyVar :: Name -> MonoKind kv -> TcVarDetails (TcDetailsThing (TcTyVar kv)) -> TcTyVar kv
mkTcTyVar name kind details = TcTyVar (TcTyVar' { _varName = name
                                                , _realUnique = nameUnique name
                                                , _varKind = kind
                                                , _tc_tv_details = details })

{- *********************************************************************
*                                                                      *
                    AnyTyVar
*                                                                      *
********************************************************************* -}

newtype AnyTyVar kv = AnyTyVar (Var Void kv)
  deriving ( Outputable, NamedThing, Uniquable, Eq, Ord, Data, HasOccName
           , VarHasName, VarHasUnique)

instance ToAnyTyVar (AnyTyVar kv) kv where
  toAnyTyVar tv = tv

instance IsVar kv => VarHasKind (AnyTyVar kv) kv where
  varKind (AnyTyVar (TyVar' { _varKind = ki })) = ki
  varKind (AnyTyVar (TcTyVar' { _varKind = ki })) = ki
  varKind other = pprPanic "Bad AnyTyVar" (ppr other)

  updateVarKind upd (AnyTyVar var@(TyVar' {}))
    = AnyTyVar (var { _varKind = upd (_varKind var) })
  updateVarKind upd (AnyTyVar var@(TcTyVar' {}))
    = AnyTyVar (var { _varKind = upd (_varKind var) })
  updateVarKind _ other = pprPanic "Bad AnyTyVar" (ppr other)

  updateVarKindM upd (AnyTyVar var) = do
    kind <- upd (_varKind var)
    return $ AnyTyVar (var { _varKind = kind })

  setVarKind (AnyTyVar tv) k = AnyTyVar (tv { _varKind = k })

  toTyVar_maybe (AnyTyVar v@(TyVar' {})) = Just $ TyVar v
  toTyVar_maybe _ = Nothing

instance ChangeVarKind AnyTyVar where
  changeVarKind upd (AnyTyVar (TyVar' {..}))
    = AnyTyVar $ TyVar' { _varKind = upd _varKind, .. }
  changeVarKind upd (AnyTyVar (TcTyVar' {..}))
    = AnyTyVar $ TcTyVar' { _varKind = upd _varKind, .. }
  changeVarKind _ other = pprPanic "Bad AnyTyVar" (ppr other)

  changeVarKindM upd (AnyTyVar (TyVar' {..})) = do
    kind <- upd _varKind
    return $ AnyTyVar $ TyVar' { _varKind = kind, .. }
  changeVarKindM upd (AnyTyVar (TcTyVar' {..})) = do
    kind <- upd _varKind
    return $ AnyTyVar $ TcTyVar' { _varKind = kind, .. }
  changeVarKindM _ other = pprPanic "Bad AnyTyVar" (ppr other)

-- instance Outputable kv => VarHasTcDetails (AnyTyVar kv) (Type (AnyTyVar kv) kv) where
--   tcVarDetails (AnyTyVar (TcTyVar' { _tc_tv_details = details })) = details
--   tcVarDetails (AnyTyVar (TyVar' {})) = vanillaSkolemTvUnk
--   tcVarDetails other = pprPanic "Bad TcKiVar" (ppr other)

instance IsKiVar kv => IsTyVar (AnyTyVar kv) kv where
  mkTyVar name kind = AnyTyVar (TyVar' { _varName = name
                                       , _realUnique = nameUnique name
                                       , _varKind = kind })
  toGenericTyVar (TyVar var) = AnyTyVar var

instance IsVar kv => ToTcTyVarMaybe (AnyTyVar kv) kv where
  toTcTyVar_maybe (AnyTyVar v@(TcTyVar' {})) = Just $ TcTyVar v
  toTcTyVar_maybe _ = Nothing

instance FromTyVar (AnyTyVar kv) kv where
  fromTv (TyVar tv) = AnyTyVar tv

instance FromTcTyVar (AnyTyVar kv) kv where
  fromTcTv (TcTyVar tv) = AnyTyVar tv

handleAnyTv :: Outputable kv => (TyVar kv -> a) -> (TcTyVar kv -> a) -> AnyTyVar kv -> a
handleAnyTv f _ (AnyTyVar tv@(TyVar' {})) = f (TyVar tv)
handleAnyTv _ f (AnyTyVar tctv@(TcTyVar' {})) = f (TcTyVar tctv)
handleAnyTv _ _ other = pprPanic "handleAnyTv" (ppr other)

{- *********************************************************************
*                                                                      *
                    KiVar
*                                                                      *
********************************************************************* -}

newtype KiVar = KiVar (Var Void Void)
  deriving ( Outputable, NamedThing, Uniquable, Eq, Ord, Data, HasOccName
           , VarHasName, VarHasUnique)

instance ToAnyKiVar KiVar where
  toAnyKiVar (KiVar kv) = AnyKiVar kv

instance IsKiVar KiVar where
  mkKiVar name = KiVar (KiVar' { _varName = name, _realUnique = nameUnique name })
  toGenericKiVar var = var

{- *********************************************************************
*                                                                      *
                    TcKiVar
*                                                                      *
********************************************************************* -}

newtype TcKiVar = TcKiVar (Var Void Void)
  deriving ( Outputable, NamedThing, Uniquable, Eq, Ord, Data, HasOccName
           , VarHasName, VarHasUnique)

instance TcVar TcKiVar where
  type TcDetailsThing TcKiVar = MonoKind AnyKiVar

  tcVarDetails (TcKiVar (TcKiVar' { _tc_kv_details = details })) = details
  tcVarDetails other = pprPanic "Bad TcKiVar" (ppr other)

  setTcVarDetails (TcKiVar v) d = TcKiVar (v { _tc_kv_details = d })

instance ToAnyKiVar TcKiVar where
  toAnyKiVar (TcKiVar var) = AnyKiVar var  

-- instance VarHasTcDetails TcKiVar (MonoKind TcKiVar) where
--   tcVarDetails (TcKiVar (TcKiVar' { _tc_kv_details = details })) = details
--   tcVarDetails other = pprPanic "Bad TcKiVar" (ppr other)

-- instance VarCanSetTcDetails TcKiVar (MonoKind TcKiVar) where
--   setTcVarDetails (TcKiVar v) d = TcKiVar (v { _tc_kv_details = d })

mkTcKiVar :: Name -> TcVarDetails (MonoKind AnyKiVar) -> TcKiVar
mkTcKiVar name details = TcKiVar (TcKiVar' { _varName = name
                                           , _realUnique = nameUnique name
                                           , _tc_kv_details = details })

{- *********************************************************************
*                                                                      *
                    AnyKiVar
*                                                                      *
********************************************************************* -}

newtype AnyKiVar = AnyKiVar (Var Void Void)
  deriving ( Outputable, NamedThing, Uniquable, Eq, Ord, Data, HasOccName
           , VarHasName, VarHasUnique)

-- instance VarHasTcDetails AnyKiVar (MonoKind AnyKiVar) where
--   tcVarDetails (AnyKiVar (TcKiVar' { _tc_kv_details = details })) = details
--   tcVarDetails (AnyKiVar (KiVar' {})) = vanillaSkolemKvUnk
--   tcVarDetails other = pprPanic "Bad TcKiVar" (ppr other)

instance ToAnyKiVar AnyKiVar where
  toAnyKiVar kv = kv

instance IsKiVar AnyKiVar where
  mkKiVar name = AnyKiVar (KiVar' { _varName = name, _realUnique = nameUnique name })
  toGenericKiVar (KiVar var) = AnyKiVar var

instance ToKiVarMaybe AnyKiVar where
  toKiVar_maybe (AnyKiVar v@(KiVar' {})) = Just $ KiVar v
  toKiVar_maybe _ = Nothing

instance ToTcKiVarMaybe AnyKiVar where
  toTcKiVar_maybe (AnyKiVar v@(TcKiVar' {})) = Just $ TcKiVar v
  toTcKiVar_maybe _ = Nothing

instance FromKiVar AnyKiVar where
  fromKv (KiVar kv) = AnyKiVar kv

instance FromTcKiVar AnyKiVar where
  fromTcKv (TcKiVar kv) = AnyKiVar kv

handleAnyKv :: (KiVar -> a) -> (TcKiVar -> a) -> AnyKiVar -> a
handleAnyKv f _ (AnyKiVar tv@(KiVar' {})) = f (KiVar tv)
handleAnyKv _ f (AnyKiVar tctv@(TcKiVar' {})) = f (TcKiVar tctv)
handleAnyKv _ _ other = pprPanic "handleAnyKv" (ppr other)

handleTcKv :: Monoid a => (TcKiVar -> a) -> AnyKiVar -> a
handleTcKv = handleAnyKv (const mempty)

filterAnyTcKiVar :: (TcKiVar -> Bool) -> [AnyKiVar] -> [TcKiVar]
filterAnyTcKiVar _ [] = []
filterAnyTcKiVar f (x:xs)
  | AnyKiVar v@(TcKiVar' {}) <- x
  , let tc_v = TcKiVar v
  , f tc_v
  = tc_v : filterAnyTcKiVar f xs
  | otherwise = filterAnyTcKiVar f xs

filterTcKiVar :: [AnyKiVar] -> [TcKiVar]
filterTcKiVar [] = []
filterTcKiVar (x:xs)
  | AnyKiVar v@(TcKiVar' {}) <- x
  , let tc_v = TcKiVar v
  = tc_v : filterTcKiVar xs
  | otherwise = filterTcKiVar xs

{- *********************************************************************
*                                                                      *
                    Id
*                                                                      *
********************************************************************* -}

newtype Id tv kv = Id (Var tv kv)
  deriving ( NamedThing, Uniquable, Eq, Ord, Data, HasOccName
           , VarHasName, VarHasUnique)

type TyCoVar = Id

deriving instance IsTyVar tv kv => Outputable (Id tv kv)
    
instance IsTyVar tv kv => VarHasType (Id tv kv) tv kv where
  varType (Id (Id' { _varType = ty })) = ty
  varType other = pprPanic "varType Bad Id" (ppr other)

  setVarType (Id id@Id'{}) ty = Id id { _varType = ty }
  setVarType other _ = pprPanic "setVarType Bad Id" (ppr other)

instance FromId (Var tv kv) tv kv where
  fromId (Id v) = v

mkGlobalVar :: IdDetails tv kv -> Name -> Type tv kv -> IdInfo -> Id tv kv
mkGlobalVar details name ty info
  = mk_id name ty GlobalId details info

mkLocalVar :: IdDetails tv kv -> Name -> Type tv kv -> IdInfo -> Id tv kv
mkLocalVar details name ty info
  = mk_id name ty (LocalId NotExported) details info

mk_id :: Name -> Type tv kv -> IdScope -> IdDetails tv kv -> IdInfo -> Id tv kv
mk_id name ty scope details info
  = Id $ Id' { _varName = name
             , _realUnique = nameUnique name
             , _varType = ty
             , _idScope = scope
             , _id_details = details
             , _id_info = info }

idInfo :: IsTyVar tv kv => Id tv kv -> IdInfo
idInfo (Id (Id' { _id_info = info })) = info
idInfo other = pprPanic "idInfo" (ppr other)

idDetails :: IsTyVar tv kv => Id tv kv -> IdDetails tv kv
idDetails (Id (Id' { _id_details = details })) = details
idDetails other = pprPanic "idDetails" (ppr other)

isGlobalId :: Id tv kv -> Bool
isGlobalId (Id (Id' { _idScope = GlobalId })) = True
isGlobalId _ = False

isExportedId :: Id tv kv -> Bool
isExportedId (Id (Id' { _idScope = GlobalId })) = True
isExportedId (Id (Id' { _idScope = LocalId Exported })) = True
isExportedId _ = False

updateIdTypeM :: Monad m => (Type tv kv -> m (Type tv kv)) -> Id tv kv -> m (Id tv kv)
updateIdTypeM f (Id id@(Id' { _varType = ty })) = do
  !ty' <- f ty
  return $ Id $ id { _varType = ty' }
updateIdTypeM _ _ = panic "updateIdTypeM"

changeIdTypeM :: Monad m => (Type tv kv -> m (Type tv' kv')) -> Id tv kv -> m (Id tv' kv')
changeIdTypeM f (Id (Id' { _varType = ty, .. })) = do
  !ty' <- f ty
  return $ Id $ Id' { _varType = ty', _id_details = panic "changeIdTypeM/idDetails", .. }
changeIdTypeM _ _ = panic "changeIdTypeM"

isLocalId :: Id tv kv -> Bool
isLocalId (Id (Id' { _idScope = LocalId _ })) = True
isLocalId _ = False

{- *********************************************************************
*                                                                      *
*                   ForAllFlag
*                                                                      *
********************************************************************* -}

data ForAllFlag
  = Optional !Specificity -- type application is optional at call sight
  | Required  -- type application is required at call sight
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

type TyVarBinder = VarBndr (TyVar KiVar) ForAllFlag

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

{- **********************************************************************
*                                                                       *
                  PiBinder
*                                                                       *
********************************************************************** -}

data PiKiBinder kv
  = Named kv
  | Anon (MonoKind kv) FunKiFlag
  deriving Data

instance Outputable kv => Outputable (PiKiBinder kv) where
  ppr (Anon ki af) = ppr af <+> ppr ki
  ppr (Named v) = ppr v

namedPiKiBinder_maybe :: PiKiBinder kv -> Maybe kv
namedPiKiBinder_maybe (Named kv) = Just kv
namedPiKiBinder_maybe _ = Nothing

data PiTyBinder tv kv
  = NamedTy (ForAllBinder tv)
  | AnonTy (Type tv kv)
  -- deriving Data

instance IsTyVar tv kv => Outputable (PiTyBinder tv kv) where
  ppr (AnonTy ty) = ppr ty
  ppr (NamedTy v) = ppr v

isInvisiblePiTyBinder :: PiTyBinder tv kv -> Bool
isInvisiblePiTyBinder (NamedTy (Bndr _ vis)) = isInvisibleForAllFlag vis
isInvisiblePiTyBinder (AnonTy _) = True

isVisiblePiTyBinder :: PiTyBinder tv kv -> Bool
isVisiblePiTyBinder = not . isInvisiblePiTyBinder
