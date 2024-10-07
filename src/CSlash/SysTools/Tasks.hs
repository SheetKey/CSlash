module CSlash.SysTools.Tasks where

-- import GHC.ForeignSrcLang

-- import GHC.CmmToLlvm.Version (LlvmVersion, llvmVersionStr, supportedLlvmVersionUpperBound, parseLlvmVersion, supportedLlvmVersionLowerBound)

import CSlash.Settings

import CSlash.SysTools.Process

import CSlash.Driver.Session

import CSlash.Utils.Exception as Exception
import CSlash.Utils.Error
import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Logger
import CSlash.Utils.TmpFs
import CSlash.Utils.Panic

import Data.List (tails, isPrefixOf)
import Data.Maybe (fromMaybe)
import System.IO
import System.Process

{- *********************************************************************
*                                                                      *
            Running an external program
*                                                                      *
********************************************************************* -}

runLlvmLlc :: Logger -> DynFlags -> [Option] -> IO ()
runLlvmLlc logger dflags args =
  let (p, args0) = pgm_lo dflags
      args1 = map Option (getOpts dflags opt_lo)
  in traceSystoolCommand logger "opt" p $
     runSomething logger "LLVM Optimizer" p (args1 ++ args ++ args0)
  
runLlvmLlc :: Logger -> DynFlags -> [Option] -> IO ()
runLlvmLlc logger dflags args =
  let (p, args0) = pgm_lc dflags
      args1 = map Option (getOpts dflags opt_lc)
  in traceSystoolCommand logger "llc" $
     runSomething logger "LLVM Compiler" p (args0 ++ args1 ++ args)

runLlvmAs :: Logger -> DynFlags -> [Option] -> IO ()
runLlvmAs logger dflags args =
  let (p, args0) = pgm_las dflags
      args1 = map Option (getOpts dflags opt_las)
  in traceSystoolCommand logger "llvm-as" $
     runSomething logger "LLVM assembler" p (args0 ++ args1 ++ args)
