{-# LANGUAGE RecordWildCards #-}

module CSlash.Unit.Module
  ( module CSlash.Unit.Types
  , module CSlash.Language.Syntax.Module.Name
  , module CSlash.Unit.Module.Location
  , module CSlash.Unit.Module.Env

  , isHoleModule
  , stableModuleCmp
  , moduleStableString
  ) where

import CSlash.Unit.Types
import CSlash.Language.Syntax.Module.Name
import CSlash.Unit.Module.Location
import CSlash.Unit.Module.Env

moduleStableString :: Module -> String
moduleStableString Module{..} =
  "$" ++ unitString moduleUnit ++ "$" ++ moduleNameString moduleName

stableModuleCmp :: Module -> Module -> Ordering
stableModuleCmp (Module p1 n1) (Module p2 n2) =
  stableUnitCmp p1 p2 <> stableModuleNameCmp n1 n2

isHoleModule :: GenModule (GenUnit u) -> Bool
isHoleModule (Module HoleUnit _) = True
isHoleModule _ = False
