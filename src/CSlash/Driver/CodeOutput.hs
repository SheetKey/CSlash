{-# LANGUAGE ScopedTypeVariables #-}

module CSlash.Driver.CodeOutput (codeOutput) where

import CSlash.Platform
-- import GHC.ForeignSrcLang
import CSlash.Data.FastString

-- import GHC.CmmToLlvm    ( llvmCodeGen )

-- import GHC.Cmm.Lint         ( cmmLint )
import CSlash.Pir
import CSlash.Pir.PLabel

import CSlash.StgToPir.CgUtils (CgStream)

import CSlash.Driver.DynFlags
import CSlash.Driver.Config.Finder ( initFinderOpts )
-- import CSlash.Driver.Config.PirToLlvm ( initLlvmCgConfig )
import CSlash.Driver.LlvmConfigCache (LlvmConfigCache)
import CSlash.Driver.Ppr
import CSlash.Driver.Backend

-- import GHC.Data.OsPath
import qualified GHC.Data.ShortText as ST
import CSlash.Data.Stream ( liftIO )
import qualified CSlash.Data.Stream as Stream

import CSlash.Utils.TmpFs

import CSlash.Utils.Error
import CSlash.Utils.Outputable
import CSlash.Utils.Logger
import CSlash.Utils.Exception ( bracket )
import CSlash.Utils.Ppr (Mode(..))
import CSlash.Utils.Panic.Plain ( pgmError )
import CSlash.Utils.Panic

import CSlash.Unit
-- import GHC.Unit.Finder      ( mkStubPaths )

import CSlash.Types.SrcLoc
-- import GHC.Types.CostCentre
-- import GHC.Types.ForeignStubs
import CSlash.Types.Unique.DSM

import System.Directory
import System.FilePath
import System.IO
import Data.Set (Set)
import qualified Data.Set as Set

{- *********************************************************************
*                                                                      *
            Steering
*                                                                      *
********************************************************************* -}

codeOutput
  :: forall a
   . Logger
  -> TmpFs
  -> LlvmConfigCache
  -> DynFlags
  -> UnitState
  -> Module
  -> FilePath
  -> ModLocation
  -> Set UnitId
  -> DUniqSupply
  -> CgStream RawPirGroup a
  -> IO (FilePath, a)
codeOutput logger tmpfs llvm_config dflags unit_state this_mode filenm location
  pkg_deps dus0 pir_stream = do


  let linted_pir_stream = if gopt Opt_DoPirLinting dflags
                          then panic "Stream.mapM (liftIO . do_lint) pir_stream"
                          else pir_stream

  let final_stream :: CgStream RawPirGroup a
      final_stream = linted_pir_stream

  let dus1 = newTagDUniqSupply 'n' dus0

  a <- outputLlvm logger llvm_config dflags filenm dus1 final_stream
  
  return (filenm, a)

doOutput :: String -> (Handle -> IO a) -> IO a
doOutput filenm io_action = bracket (openFile filenm WriteMode) hClose io_action

{- *********************************************************************
*                                                                      *
            LLVM
*                                                                      *
********************************************************************* -}

outputLlvm
  :: Logger
  -> LlvmConfigCache
  -> DynFlags
  -> FilePath
  -> DUniqSupply
  -> CgStream RawPirGroup a
  -> IO a
outputLlvm logger llvm_config dflags filenm dus pir_stream = do
  lcg_config <- initLlvmCgConfig logger llvm_config dflags
  {-# SCC "llvm_output" #-} doOutput filenm $
    \f -> {-# SCC "llvm_CodeGen" #-}
      llvmCodeGen logger lcg_config f dus pir_stream
