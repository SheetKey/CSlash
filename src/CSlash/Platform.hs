module CSlash.Platform where

-- import GHC.Read
import CSlash.ByteOrder (ByteOrder(..))
-- import GHC.Platform.Constants
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
  , platformTableNextToCode :: !Bool
  , platformHasLibm :: !Bool
  , platform_constants :: !(Maybe PlatformConstants)
  }
  deriving (Show, Eq, Ord)

-- -----------------------------------------------------------------------------
-- Platform Constants

data PlatformWordSize
  = PW4
  | PW8

instance Show PlatformWordSize where
  show PW4 = "4"
  show PW8 = "8"

data PlatformMisc = PlatformMisc
