module CSlash.Types.Id
  ( Id

  , idName

  , mkGlobalId, mkLocalId
  ) where

import CSlash.Types.Id.Info
import CSlash.Types.Basic

import CSlash.Types.Var (Id)
import qualified CSlash.Types.Var as Var

import CSlash.Core.Type
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

idName :: Id tv kv -> Name
idName = Var.varName

mkGlobalId :: IdDetails tv kv -> Name -> Type tv kv -> IdInfo -> Id tv kv
mkGlobalId = Var.mkGlobalVar

mkLocalId :: Name -> Type tv kv -> Id tv kv
mkLocalId name ty = mkLocalIdWithInfo name ty vanillaIdInfo

mkLocalIdWithInfo :: Name -> Type tv kv -> IdInfo -> Id tv kv
mkLocalIdWithInfo name ty info = Var.mkLocalVar VanillaId name ty info
