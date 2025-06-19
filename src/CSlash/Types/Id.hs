module CSlash.Types.Id
  ( Var, Id

  , idName

  , mkGlobalId
  ) where

import CSlash.Types.Id.Info
import CSlash.Types.Basic

import CSlash.Types.Var (Var, Id)
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
