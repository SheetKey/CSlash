module CSlash.Linker.Types where

import CSlash.Unit              ( UnitId, Module )
-- import GHC.ByteCode.Types    ( ItblEnv, AddrEnv, CompiledByteCode )
import CSlash.Utils.Fingerprint ( Fingerprint )
-- import GHCi.RemoteTypes      ( ForeignHValue )

import CSlash.Types.Var         ( Id )
import CSlash.Types.Name.Env    ( NameEnv, emptyNameEnv, extendNameEnvList, filterNameEnv )
import CSlash.Types.Name        ( Name )

import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Control.Concurrent.MVar
import Data.Time                ( UTCTime )
import Data.Maybe
import CSlash.Unit.Module.Env
import CSlash.Types.Unique.DSet
import CSlash.Types.Unique.DFM
-- import GHC.Unit.Module.WholeCoreBindings

{- ********************************************************************

                        The Loader's state

********************************************************************* -}

data Linkable = LM
  { linkableTime :: !UTCTime
  , linkableModule :: !Module
  , linkableUnlinked :: [Unlinked]
  }

type ObjFile = FilePath

data Unlinked
  = DotO ObjFile
  | DotA FilePath
  | DotSO FilePath

data SptEntry = SptEntry Id Fingerprint
