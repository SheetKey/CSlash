module CSlash.Types.Id
  ( Id, Var.varType

  , module CSlash.Types.Id
  ) where

import CSlash.Types.Id.Info
import CSlash.Types.Basic

import CSlash.Types.Var (Id)
import qualified CSlash.Types.Var as Var

import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Core.Predicate
import CSlash.Types.RepType
import CSlash.Core.DataCon
import CSlash.Types.Name
import CSlash.Unit.Module
import CSlash.Data.Maybe
import CSlash.Types.SrcLoc
import CSlash.Types.Unique
import CSlash.Data.FastString

import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

type AnyId = Id (AnyTyVar AnyKiVar) AnyKiVar
type ZkId = Id (TyVar KiVar) KiVar

idName :: Id tv kv -> Name
idName = Var.varName

mkGlobalId :: IdDetails tv kv -> Name -> Type tv kv -> IdInfo -> Id tv kv
mkGlobalId = Var.mkGlobalVar

mkLocalId :: Name -> Type tv kv -> Id tv kv
mkLocalId name ty = mkLocalIdWithInfo name ty vanillaIdInfo

mkLocalIdWithInfo :: Name -> Type tv kv -> IdInfo -> Id tv kv
mkLocalIdWithInfo name ty info = Var.mkLocalVar VanillaId name ty info

mkLocalTyCoVar
  :: Name -> PredType (AnyTyVar AnyKiVar) AnyKiVar -> TyCoVar (AnyTyVar AnyKiVar) AnyKiVar
mkLocalTyCoVar name ty = assert (isTyCoVarType ty)
                         $ Var.mkLocalVar TyCoVarId name ty vanillaIdInfo

mkLocalIdOrTyCoVar
  :: Name -> Type (AnyTyVar AnyKiVar) AnyKiVar -> Id (AnyTyVar AnyKiVar) AnyKiVar
mkLocalIdOrTyCoVar name ty
  | isTyCoVarType ty = mkLocalTyCoVar name ty
  | otherwise = mkLocalId name ty

idOccInfo :: Var.IsTyVar tv kv => Id tv kv -> OccInfo
idOccInfo id = occInfo (Var.idInfo id)

isDeadBinder :: Var.IsTyVar tv kv => Id tv kv -> Bool
isDeadBinder bndr = isDeadOcc (idOccInfo bndr)

idKind :: Var.IsTyVar tv kv => Id tv kv -> Kind kv
idKind = typeKind . Var.varType

{- *********************************************************************
*                                                                      *
            Special Ids
*                                                                      *
********************************************************************* -}

isDataConId_maybe :: Var.IsTyVar tv kv => Id tv kv -> Maybe (DataCon tv kv)
isDataConId_maybe id = case Var.idDetails id of
                         DataConId con -> Just con
                         _ -> Nothing
