module CSlash.Unit.Module.Imported
  ( ImportedMods
  , ImportedBy(..)
  , ImportedModsVal(..)
  , importedByUser
  ) where

import CSlash.Unit.Module

import CSlash.Types.Name.Reader
import CSlash.Types.SrcLoc

type ImportedMods = ModuleEnv [ImportedBy]

data ImportedBy
    = ImportedByUser ImportedModsVal
    | ImportedBySystem

importedByUser :: [ImportedBy] -> [ImportedModsVal]
importedByUser (ImportedByUser imv : bys) = imv : importedByUser bys
importedByUser (ImportedBySystem   : bys) =       importedByUser bys
importedByUser [] = []

data ImportedModsVal = ImportedModsVal
   { imv_name        :: ModuleName
   , imv_span        :: SrcSpan
   , imv_is_hiding   :: Bool
   , imv_all_exports :: !GlobalRdrEnv
   , imv_qualified   :: Bool
   }
