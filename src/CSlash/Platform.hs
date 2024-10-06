{-# LANGUAGE ScopedTypeVariables #-}

module CSlash.Platform
  ( Platform(..)
  , PlatformWordSize(..)
  , platformArch
  , platformOS
  , ArchOS(..)
  , Arch(..)
  , OS(..)
  , ByteOrder(..)
  , target32Bit
  , osElfTarget
  , PlatformMisc(..)
  , PlatformConstants(..)
  ) where

import GHC.Read

import CSlash.ByteOrder (ByteOrder(..))
import CSlash.Platform.Constants
import CSlash.Platform.ArchOS
import CSlash.Types.Basic (Alignment, alignmentOf)
import CSlash.Utils.Panic.Plain

import Data.Word
import Data.Int
import System.FilePath
import System.Directory

data Platform = Platform
  { platformArchOS :: !ArchOS 
  , platformWordSize :: !PlatformWordSize
  , platformByteOrder :: !ByteOrder
  , platformUnregisterised :: !Bool
  , platformHasGnuNoexecStack :: !Bool
  , platformHasIdentDirective :: !Bool
  , platformHasSubsectionsViaSymbols :: !Bool
  , platformIsCrossCompiling :: !Bool
  , platformLeadingUnderscore :: !Bool
  , platformTablesNextToCode :: !Bool
  , platformHasLibm :: !Bool
  , platform_constants :: !(Maybe PlatformConstants)
  }
  deriving (Show, Eq, Ord, Read)

-- -----------------------------------------------------------------------------
-- Platform Constants

data PlatformWordSize
  = PW4
  | PW8
  deriving (Eq, Ord)

instance Show PlatformWordSize where
  show PW4 = "4"
  show PW8 = "8"

instance Read PlatformWordSize where
  readPrec = do
    i :: Int <- readPrec
    case i of
      4 -> return PW4
      8 -> return PW8
      other -> fail ("Invalid PlatformWordSize: " ++ show other)

platformArch :: Platform -> Arch
platformArch platform = case platformArchOS platform of
  ArchOS arch _ -> arch

platformOS :: Platform -> OS
platformOS platform = case platformArchOS platform of
  ArchOS _ os -> os

target32Bit :: Platform -> Bool
target32Bit p =
  case platformWordSize p of
    PW4 -> True
    PW8 -> False
  

data PlatformMisc = PlatformMisc
  { platformMisc_targetPlatformString :: String
  , platformMisc_llvmTarget :: String
  }
