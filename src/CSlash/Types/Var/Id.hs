{-# LANGUAGE RecordWildCards #-}

module CSlash.Types.Var.Id where

import {-# SOURCE #-} CSlash.Core.Type (typeKind)
import {-# SOURCE #-} CSlash.Core.Type.Rep (Type, PredType)
import {-# SOURCE #-} CSlash.Core.Kind (Kind, MonoKind)
import {-# SOURCE #-} CSlash.Tc.Utils.TcType (TcVarDetails, pprTcVarDetails)
import {-# SOURCE #-} CSlash.Types.Var.Id.Info (IdDetails, IdInfo, pprIdDetails)

import CSlash.Cs.Pass

import CSlash.Types.Var.Class
import CSlash.Types.Var.Id.Info

import CSlash.Types.Name hiding (varName)
import CSlash.Types.Unique
import CSlash.Types.Basic

import {-# SOURCE #-} CSlash.Core.DataCon

import CSlash.Utils.Outputable
import CSlash.Utils.Misc

import Data.Data

data Id p
  = Id
    { id_name :: !Name
    , id_real_unique :: {-# UNPACK #-} !Unique
    , id_type :: Type p
    , id_scope :: IdScope
    , id_details :: IdDetails
    , id_info :: IdInfo
    }

data IdScope
  = GlobalId
  | LocalId ExportFlag

data ExportFlag
  = NotExported
  | Exported

instance IsVar (Id p) where
  varName = id_name
  setVarName id name = id { id_name = name }

  varUnique = id_real_unique
  setVarUnique id unique = id { id_real_unique = unique }

instance Outputable (Id p)

instance (Typeable p) => Data (Id p) where
  toConstr _ = abstractConstr "Id"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "Id"

instance Eq (Id p) where
  a == b = id_real_unique a == id_real_unique b

instance Ord (Id p) where
  a <= b = getKey (id_real_unique a) <= getKey (id_real_unique b)
  a < b = getKey (id_real_unique a) < getKey (id_real_unique b)
  a >= b = getKey (id_real_unique a) >= getKey (id_real_unique b)
  a > b = getKey (id_real_unique a) > getKey (id_real_unique b)
  a `compare` b = id_real_unique a `nonDetCmpUnique` id_real_unique b

instance NamedThing (Id p)

instance Uniquable (Id p)

instance VarHasType Id

mk_id :: Name -> Type p -> IdScope -> IdDetails -> IdInfo -> Id p
mk_id name ty scope details info = Id { id_name = name
                                      , id_real_unique = nameUnique name
                                      , id_type = ty
                                      , id_scope = scope
                                      , id_details = details
                                      , id_info = info }

mkGlobalId :: IdDetails -> Name -> Type p -> IdInfo -> Id p
mkGlobalId details name ty info = mk_id name ty GlobalId details info

mkLocalId :: Name -> Type p -> Id p
mkLocalId name ty = mkLocalIdWithInfo name ty vanillaIdInfo

mkLocalIdWithInfo :: Name -> Type p -> IdInfo -> Id p
mkLocalIdWithInfo name ty info = mk_id name ty (LocalId NotExported) VanillaId info

idInfo :: Id p -> IdInfo
idInfo = id_info

idDetails :: Id p -> IdDetails
idDetails = id_details

idOccInfo :: Id p -> OccInfo
idOccInfo id = occInfo (idInfo id)

isDeadBinder :: Id p -> Bool
isDeadBinder bndr = isDeadOcc (idOccInfo bndr)

idKind :: Id p -> Kind p
idKind = typeKind . varType

changeIdTypeM :: Monad m => (Type p -> m (Type p')) -> Id p -> m (Id p')
changeIdTypeM f (Id { id_type = ty, .. }) = do
  ty' <- f ty
  return $ Id { id_type = ty', .. }

{- *********************************************************************
*                                                                      *
            Special Ids
*                                                                      *
********************************************************************* -}

isDataConId_maybe :: Id p -> Maybe (DataCon Zk)
isDataConId_maybe id = case idDetails id of
                         DataConId con -> Just con
                         _ -> Nothing

isGlobalId :: Id p -> Bool
isGlobalId (Id {id_scope = GlobalId }) = True
isGlobalId _ = False

isExportedId :: Id p -> Bool
isExportedId (Id { id_scope = GlobalId }) = True
isExportedId (Id { id_scope = LocalId Exported }) = True
isExportedId _ = False

isLocalId :: Id p -> Bool
isLocalId (Id { id_scope = LocalId _ }) = True
isLocalId _ = False
