module CSlash.Linker.ExtraObj where

import CSlash.Platform

import CSlash.Unit
import CSlash.Unit.Env

-- import GHC.Utils.Asm
import CSlash.Utils.Error
import CSlash.Utils.Misc
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Logger
import CSlash.Utils.TmpFs

import CSlash.Driver.Session
import CSlash.Driver.Ppr

import qualified GHC.Data.ShortText as ST

-- import GHC.SysTools.Elf
import CSlash.SysTools.Tasks
import CSlash.Linker.Unit

import Control.Monad
import Data.Maybe

haveRtsOptsFlags :: DynFlags -> Bool
haveRtsOptsFlags dflags = isJust (rtsOpts dflags)
                          || case rtsOptsEnabled dflags of
                               RtsOptsSafeOnly -> False
                               _ -> True
