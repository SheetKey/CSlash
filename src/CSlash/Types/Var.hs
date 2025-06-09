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
  , VarHasType(..), VarHasKind(..)
  , VarHasTcDetails(..), VarCanSetTcDetails(..)
  , ToVar(..), ToAnyTyVar(..), ToAnyKiVar(..)
  , ToTyVarMaybe(..), ToTcTyVarMaybe(..), ToAnyTyVarMaybe(..)
  , ToKiVarMaybe(..), ToTcKiVarMaybe(..), ToAnyKiVarMaybe(..)
  , ToIdMaybe(..)
  , FromTyVar(..), FromTcTyVar(..), FromAnyTyVar(..)
  , FromKiVar(..), FromTcKiVar(..), FromAnyKiVar(..)
  , FromId(..)

    {-* TyVar *-}
  , TyVar, KiCoVar
  , mkTyVar

    {-* TcTyVar *-}
  , TcTyVar, TcKiCoVar

    {-* AnyTyVar *-}
  , AnyTyVar, AnyKiCoVar

    {-* KiVar *-}
  , KiVar
  , mkKiVar

    {-* TcKiVar *-}
  , TcKiVar

    {-* AnyKiVar *-}
  , AnyKiVar

    {-* Id *-}
  , Id

    {-* ForAllFlag *-}
  , ForAllFlag(..)
  , isVisibleForAllFlag, isInvisibleForAllFlag
  
    {-* VarBndr *-}
  , VarBndr(..), ForAllBinder, TyVarBinder
  , binderVar, binderVars
  , mkVarBinder, mkVarBinders
  ) where

import Prelude hiding ((<>))

import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import {-# SOURCE #-} CSlash.Core.Type.Ppr (pprType)
import {-# SOURCE #-} CSlash.Core.Kind (Kind, MonoKind, pprKind, isCoVarKind)
import {-# SOURCE #-} CSlash.Tc.Utils.TcType
  ( TcTyVarDetails, TcKiVarDetails
  , pprTcTyVarDetails, pprTcKiVarDetails
  , vanillaSkolemTvUnk, vanillaSkolemKvUnk)
import {-# SOURCE #-} CSlash.Types.Id.Info (IdDetails, IdInfo, pprIdDetails)

import CSlash.Types.Name hiding (varName)
import CSlash.Types.Unique ( Uniquable, Unique, getKey, getUnique, nonDetCmpUnique )

import CSlash.Utils.Misc
import CSlash.Utils.Binary
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

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
    , _tc_tv_details :: TcTyVarDetails
    }
  | KiVar'
    { _varName :: !Name
    , _realUnique :: {-# UNPACK #-} !Unique
    }
  | TcKiVar' -- for kind inference
    { _varName :: !Name
    , _realUnique :: {-# UNPACK #-} !Unique
    , _tc_kv_details :: TcKiVarDetails
    }
  | Id'
    { _varName :: !Name
    , _realUnique :: {-# UNPACK #-} !Unique
    , _varType :: Type tv kv
    , _idScope :: IdScope
    , _id_details :: IdDetails
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
            -> brackets (pprTcTyVarDetails d)
          (TcKiVar' { _tc_kv_details = d })
            | dumpStyle sty || debug
            -> brackets (pprTcKiVarDetails d)
          _ -> empty
        ppr_tyki = case var of
          (TyVar' { _varKind = ki }) -> char ' ' <> colon <+> ppr ki
          (TcTyVar' { _varKind = ki }) -> char ' ' <> colon <+> ppr ki
          _ -> empty

    in if debug
       then parens (ppr (_varName var) <+> ppr_var <> ppr_tyki)
       else ppr (_varName var) <> ppr_var
    
instance VarHasKind tv kv => Outputable (Var tv kv) where
  ppr var = 
    getPprDebug $ \ debug ->
    getPprStyle $ \ sty ->
    let ppr_var = case var of
          (TyVar' {}) | debug -> brackets (text "tv")
          (KiVar' {}) | debug -> brackets (text "kv")
          (TcTyVar' { _tc_tv_details = d })
            | dumpStyle sty || debug
            -> brackets (pprTcTyVarDetails d)
          (TcKiVar' { _tc_kv_details = d })
            | dumpStyle sty || debug
            -> brackets (pprTcKiVarDetails d)
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
  updateVarKind :: (MonoKind kv -> MonoKind kv) -> v -> v
  updateVarKindM :: Monad m => (MonoKind kv -> m (MonoKind kv)) -> v -> m v
  setVarKind :: v -> (MonoKind kv) -> v

class VarHasTcDetails v d | v -> d where
  tcVarDetails :: v -> d

class VarCanSetTcDetails v d | v -> d where
  setTcVarDetails :: v -> d -> v

class ToTyVarMaybe v kv | v -> kv where
  toTyVar_maybe :: v -> Maybe (TyVar kv)

instance ToTyVarMaybe (Var tv kv) kv where
  toTyVar_maybe tv@(TyVar' {}) = Just $ TyVar $ vacuousFirst' tv
  toTyVar_maybe _ = Nothing

class ToTcTyVarMaybe v tv | v -> tv where
  toTcTyVar_maybe :: v -> Maybe (TcTyVar tv)

instance ToTcTyVarMaybe (Var tv kv) kv where
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

class ToTcKiVarMaybe v where
  toTcKiVar_maybe :: v -> Maybe TcKiVar

instance ToTcKiVarMaybe (Var tv kv) where
  toTcKiVar_maybe kv@(TcKiVar' {}) = Just $ TcKiVar $ vacuousBimap' kv
  toTcKiVar_maybe _ = Nothing

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

class ToAnyKiVar v where
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

{- *********************************************************************
*                                                                      *
                    TyVar
*                                                                      *
********************************************************************* -}

newtype TyVar kv = TyVar (Var Void kv)
  deriving ( Outputable, NamedThing, Uniquable, Eq, Ord, Data, HasOccName
           , VarHasName, VarHasUnique)

type KiCoVar = TyVar

instance IsVar kv => VarHasKind (TyVar kv) kv where
  varKind (TyVar (TyVar' { _varKind = ki })) = ki
  varKind other = pprPanic "Bad TyVar" (ppr other)

  updateVarKind upd (TyVar var@(TyVar' {})) = TyVar (var { _varKind = upd (_varKind var) })
  updateVarKind _ other = pprPanic "Bad TyVar" (ppr other)

mkTyVar :: Name -> MonoKind kv -> TyVar kv
mkTyVar name kind = TyVar (TyVar' { _varName = name
                                  , _realUnique = nameUnique name
                                  , _varKind = kind })

{- *********************************************************************
*                                                                      *
                    TcyTyVar
*                                                                      *
********************************************************************* -}

newtype TcTyVar kv = TcTyVar (Var Void kv)
  deriving ( Outputable, NamedThing, Uniquable, Eq, Ord, Data, HasOccName
           , VarHasName, VarHasUnique)
  
type TcKiCoVar = TcTyVar

instance IsVar kv => VarHasKind (TcTyVar kv) kv where
  varKind (TcTyVar (TcTyVar' { _varKind = ki })) = ki
  varKind other = pprPanic "Bad TcTyVar" (ppr other)

  updateVarKind upd (TcTyVar var@(TcTyVar' {}))
    = TcTyVar (var { _varKind = upd (_varKind var) })
  updateVarKind _ other = pprPanic "Bad TcTyVar" (ppr other)

instance Outputable kv => VarHasTcDetails (TcTyVar kv) TcTyVarDetails where
  tcVarDetails (TcTyVar (TcTyVar' { _tc_tv_details = details })) = details
  tcVarDetails other = pprPanic "Bad TcKiVar" (ppr other)

instance VarCanSetTcDetails (TcTyVar kv) TcTyVarDetails where
  setTcVarDetails (TcTyVar v) d = TcTyVar (v { _tc_tv_details = d })

mkTcTyVar :: Name -> MonoKind kv -> TcTyVarDetails -> TcTyVar kv
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

type AnyKiCoVar = AnyTyVar

instance IsVar kv => VarHasKind (AnyTyVar kv) kv where
  varKind (AnyTyVar (TyVar' { _varKind = ki })) = ki
  varKind (AnyTyVar (TcTyVar' { _varKind = ki })) = ki
  varKind other = pprPanic "Bad AnyTyVar" (ppr other)

  updateVarKind upd (AnyTyVar var@(TyVar' {}))
    = AnyTyVar (var { _varKind = upd (_varKind var) })
  updateVarKind upd (AnyTyVar var@(TcTyVar' {}))
    = AnyTyVar (var { _varKind = upd (_varKind var) })
  updateVarKind _ other = pprPanic "Bad AnyTyVar" (ppr other)

instance Outputable kv => VarHasTcDetails (AnyTyVar kv) TcTyVarDetails where
  tcVarDetails (AnyTyVar (TcTyVar' { _tc_tv_details = details })) = details
  tcVarDetails (AnyTyVar (TyVar' {})) = vanillaSkolemTvUnk
  tcVarDetails other = pprPanic "Bad TcKiVar" (ppr other)

instance ToTyVarMaybe (AnyTyVar kv) kv where
  toTyVar_maybe (AnyTyVar v@(TyVar' {})) = Just $ TyVar v
  toTyVar_maybe _ = Nothing

instance ToTcTyVarMaybe (AnyTyVar kv) kv where
  toTcTyVar_maybe (AnyTyVar v@(TcTyVar' {})) = Just $ TcTyVar v
  toTcTyVar_maybe _ = Nothing

instance FromTyVar (AnyTyVar kv) kv where
  fromTv (TyVar tv) = AnyTyVar tv

instance FromTcTyVar (AnyTyVar kv) kv where
  fromTcTv (TcTyVar tv) = AnyTyVar tv

{- *********************************************************************
*                                                                      *
                    KiVar
*                                                                      *
********************************************************************* -}

newtype KiVar = KiVar (Var Void Void)
  deriving ( Outputable, NamedThing, Uniquable, Eq, Ord, Data, HasOccName
           , VarHasName, VarHasUnique)

mkKiVar :: Name -> KiVar
mkKiVar name = KiVar (KiVar' { _varName = name, _realUnique = nameUnique name })

{- *********************************************************************
*                                                                      *
                    TcKiVar
*                                                                      *
********************************************************************* -}

newtype TcKiVar = TcKiVar (Var Void Void)
  deriving ( Outputable, NamedThing, Uniquable, Eq, Ord, Data, HasOccName
           , VarHasName, VarHasUnique)

instance VarHasTcDetails TcKiVar TcKiVarDetails where
  tcVarDetails (TcKiVar (TcKiVar' { _tc_kv_details = details })) = details
  tcVarDetails other = pprPanic "Bad TcKiVar" (ppr other)

instance VarCanSetTcDetails TcKiVar TcKiVarDetails where
  setTcVarDetails (TcKiVar v) d = TcKiVar (v { _tc_kv_details = d })

mkTcKiVar :: Name -> TcKiVarDetails -> TcKiVar
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

instance VarHasTcDetails AnyKiVar TcKiVarDetails where
  tcVarDetails (AnyKiVar (TcKiVar' { _tc_kv_details = details })) = details
  tcVarDetails (AnyKiVar (KiVar' {})) = vanillaSkolemKvUnk
  tcVarDetails other = pprPanic "Bad TcKiVar" (ppr other)

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

{- *********************************************************************
*                                                                      *
                    Id
*                                                                      *
********************************************************************* -}

newtype Id tv kv = Id (Var tv kv)
  deriving ( NamedThing, Uniquable, Eq, Ord, Data, HasOccName
           , VarHasName, VarHasUnique)

deriving instance VarHasKind tv kv => Outputable (Id tv kv)
    
instance VarHasKind tv kv => VarHasType (Id tv kv) tv kv where
  varType (Id (Id' { _varType = ty })) = ty
  varType other = pprPanic "Bad Id" (ppr other)

instance FromId (Var tv kv) tv kv where
  fromId (Id v) = v

{- *********************************************************************
*                                                                      *
*                   ForAllFlag
*                                                                      *
********************************************************************* -}

data ForAllFlag
  = Specified -- type application is optional at call sight
  | Required  -- type application is required at call sight
  deriving (Eq, Ord, Data)

isVisibleForAllFlag :: ForAllFlag -> Bool
isVisibleForAllFlag af = not (isInvisibleForAllFlag af)

isInvisibleForAllFlag :: ForAllFlag -> Bool
isInvisibleForAllFlag Specified = True
isInvisibleForAllFlag Required = False

instance Outputable ForAllFlag where
  ppr Required  = text "[req]"
  ppr Specified = text "[spec]"

instance Binary ForAllFlag where
  put_ bh Required  = putByte bh 0
  put_ bh Specified = putByte bh 1

  get bh = do
    h <- getByte bh
    case h of
      0 -> return Required
      _ -> return Specified

{- *********************************************************************
*                                                                      *
                   VarBndr, ForAllBinder
*                                                                      *
********************************************************************* -}

data VarBndr var argf = Bndr var argf
  deriving Data

type ForAllBinder var = VarBndr var ForAllFlag

type TyVarBinder = VarBndr (TyVar KiVar) ForAllFlag

binderVar :: VarBndr v argf -> v
binderVar (Bndr v _) = v

binderVars :: [VarBndr v argf] -> [v]
binderVars bvs = map binderVar bvs

mkVarBinder :: argf -> var -> VarBndr var argf
mkVarBinder argf var = Bndr var argf

mkVarBinders :: argf -> [var] -> [VarBndr var argf]
mkVarBinders argf = map (mkVarBinder argf)
