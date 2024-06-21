{-# LANGUAGE KindSignatures #-}

module CSlash.Unit.Types where

import CSlash.Language.Syntax.Module.Name (ModuleName)
import Data.Kind (Type)

data UnitId
data GenModule (unit :: Type)
data GenUnit (uid :: Type)

type Module = GenModule Unit
type Unit = GenUnit UnitId

moduleName :: GenModule a -> ModuleName
moduleUnit :: GenModule a -> a