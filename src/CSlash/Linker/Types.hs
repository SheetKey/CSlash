module CSlash.Linker.Types where

import CSlash.Cs.Pass           ( Zk )

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

instance Outputable Linkable where
  ppr (LM when_made mod unlinkeds)
    = (text "LinkableM" <+> parens (text (show when_made)) <+> ppr mod)
      $$ nest 3 (ppr unlinkeds)

type ObjFile = FilePath

data Unlinked
  = DotO ObjFile
  | DotA FilePath
  | DotSO FilePath

instance Outputable Unlinked where
  ppr (DotO path) = text "DotO" <+> text path
  ppr (DotA path) = text "DotA" <+> text path
  ppr (DotSO path) = text "DotSO" <+> text path

data SptEntry = SptEntry (Id Zk) Fingerprint

isObjectLinkable :: Linkable -> Bool
isObjectLinkable l = not (null unlinked) && all isObject unlinked
  where
    unlinked = linkableUnlinked l

isObject :: Unlinked -> Bool
isObject (DotO _) = True
isObject (DotA _) = True
isObject (DotSO _) = True
isObject _ = False
