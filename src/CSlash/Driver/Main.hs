module CSlash.Driver.Main
  ( module CSlash.Driver.Main
  , CsBackendAction(..), CsRecompStatus(..)
  ) where

import CSlash.Platform

-- import GHC.Driver.Plugins
import CSlash.Driver.Session
import CSlash.Driver.Backend
import CSlash.Driver.Env
import CSlash.Driver.Env.KnotVars
import CSlash.Driver.Errors
import CSlash.Driver.Errors.Types
-- import CSlash.Driver.CodeOutput
-- import GHC.Driver.Config.Cmm.Parser (initCmmParserConfig)
-- import GHC.Driver.Config.Core.Opt.Simplify ( initSimplifyExprOpts )
-- import GHC.Driver.Config.Core.Lint ( endPassHscEnvIO )
-- import GHC.Driver.Config.Core.Lint.Interactive ( lintInteractiveExpr )
-- import GHC.Driver.Config.CoreToStg
-- import GHC.Driver.Config.CoreToStg.Prep
import CSlash.Driver.Config.Logger   (initLogFlags)
import CSlash.Driver.Config.Parser   (initParserOpts)
-- import GHC.Driver.Config.Stg.Ppr  (initStgPprOpts)
-- import GHC.Driver.Config.Stg.Pipeline (initStgPipelineOpts)
-- import GHC.Driver.Config.StgToCmm  (initStgToCmmConfig)
-- import GHC.Driver.Config.Cmm       (initCmmConfig)
import CSlash.Driver.LlvmConfigCache  (initLlvmConfigCache)
-- import GHC.Driver.Config.StgToJS  (initStgToJSConfig)
import CSlash.Driver.Config.Diagnostic
-- import GHC.Driver.Config.Tidy
-- import GHC.Driver.Hooks
-- import GHC.Driver.GenerateCgIPEStub (generateCgIPEStub, lookupEstimatedTicks)

-- import GHC.Runtime.Context
-- import GHC.Runtime.Interpreter
-- import GHC.Runtime.Interpreter.JS
-- import GHC.Runtime.Loader      ( initializePlugins )
-- import GHCi.RemoteTypes
-- import GHC.ByteCode.Types

-- import GHC.Linker.Loader
import CSlash.Linker.Types
-- import GHC.Linker.Deps

import CSlash.Cs
import CSlash.Cs.Dump
import CSlash.Cs.Stats         ( ppSourceStats )

-- import GHC.HsToCore

-- import GHC.StgToByteCode    ( byteCodeGen )
-- import GHC.StgToJS          ( stgToJS )
-- import GHC.StgToJS.Ids
-- import GHC.StgToJS.Types
-- import GHC.JS.Syntax

-- import GHC.IfaceToCore  ( typecheckIface, typecheckWholeCoreBindings )

-- import GHC.Iface.Load   ( ifaceStats, writeIface )
-- import GHC.Iface.Make
import CSlash.Iface.Recomp
-- import GHC.Iface.Tidy
-- import GHC.Iface.Ext.Ast    ( mkHieFile )
-- import GHC.Iface.Ext.Types  ( getAsts, hie_asts, hie_module )
-- import GHC.Iface.Ext.Binary ( readHieFile, writeHieFile , hie_file_result)
-- import GHC.Iface.Ext.Debug  ( diffFile, validateScopes )

import CSlash.Core
-- import GHC.Core.Lint.Interactive ( interactiveInScope )
-- import GHC.Core.Tidy           ( tidyExpr )
-- import GHC.Core.Utils          ( exprType )
import CSlash.Core.ConLike
-- import GHC.Core.Opt.Pipeline
-- import GHC.Core.Opt.Pipeline.Types      ( CoreToDo (..))
import CSlash.Core.TyCon
-- import GHC.Core.InstEnv
-- import GHC.Core.FamInstEnv
-- import GHC.Core.Rules
-- import GHC.Core.Stats
-- import GHC.Core.LateCC
-- import GHC.Core.LateCC.Types

-- import GHC.CoreToStg.Prep
-- import GHC.CoreToStg    ( coreToStg )

import CSlash.Parser.Errors.Types
import CSlash.Parser
import CSlash.Parser.Lexer as Lexer

import CSlash.Tc.Module
import CSlash.Tc.Utils.Monad
-- import GHC.Tc.Utils.TcType
-- import GHC.Tc.Zonk.Env ( ZonkFlexi (DefaultFlexi) )

-- import GHC.Stg.Syntax
-- import GHC.Stg.Pipeline ( stg2stg, StgCgInfos )

import CSlash.Builtin.Utils
import CSlash.Builtin.Names

-- import qualified GHC.StgToCmm as StgToCmm ( codeGen )
-- import GHC.StgToCmm.Types (CmmCgInfos (..), ModuleLFInfos, LambdaFormInfo(..))

-- import GHC.Cmm
-- import GHC.Cmm.Info.Build
-- import GHC.Cmm.Pipeline
-- import GHC.Cmm.Info
-- import GHC.Cmm.Parser

import CSlash.Unit
import CSlash.Unit.Env
import CSlash.Unit.Finder
import CSlash.Unit.External
import CSlash.Unit.Module.ModDetails
import CSlash.Unit.Module.ModGuts
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.ModSummary
import CSlash.Unit.Module.Graph
import CSlash.Unit.Module.Imported
import CSlash.Unit.Module.Deps
import CSlash.Unit.Module.Status
import CSlash.Unit.Home.ModInfo

import CSlash.Types.Id
import CSlash.Types.SourceError
-- import GHC.Types.SafeHaskell
-- import GHC.Types.ForeignStubs
import CSlash.Types.Name.Env      ( mkNameEnv )
import CSlash.Types.Var.Env       ( mkEmptyTidyEnv )
import CSlash.Types.Var.Set
import CSlash.Types.Error
import CSlash.Types.Fixity.Env
-- import GHC.Types.CostCentre
-- import GHC.Types.IPE
import CSlash.Types.SourceFile
import CSlash.Types.SrcLoc
import CSlash.Types.Name
import CSlash.Types.Name.Cache ( initNameCache )
import CSlash.Types.Name.Reader
-- import GHC.Types.Name.Ppr
import CSlash.Types.TyThing
-- import GHC.Types.HpcInfo
import CSlash.Types.Unique.Supply (uniqFromTag)
import CSlash.Types.Unique.Set

import CSlash.Utils.Fingerprint ( Fingerprint )
import CSlash.Utils.Panic
import CSlash.Utils.Error
import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Logger
import CSlash.Utils.TmpFs
-- import GHC.Utils.Touch

-- import qualified GHC.LanguageExtensions as LangExt

import CSlash.Data.FastString
import CSlash.Data.Bag
import CSlash.Data.StringBuffer
-- import qualified GHC.Data.Stream as Stream
-- import GHC.Data.Stream (Stream)
import CSlash.Data.Maybe

import CSlash.SysTools (initSysTools)
import CSlash.SysTools.BaseDir (findTopDir)

import Data.Data hiding (Fixity, TyCon)
import Data.List        ( nub, isPrefixOf, partition )
import qualified Data.List.NonEmpty as NE
import Control.Monad
import Data.IORef
import System.FilePath as FilePath
import System.Directory
import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.Set as S
import Data.Set (Set)
import Control.DeepSeq (force)
import Data.List.NonEmpty (NonEmpty ((:|)))

-- import GHC.Unit.Module.WholeCoreBindings
import CSlash.Types.TypeEnv
import System.IO
-- import {-# SOURCE #-} GHC.Driver.Pipeline
import Data.Time

import System.IO.Unsafe ( unsafeInterleaveIO )

import CSlash.Iface.Env ( trace_if )
-- import GHC.Stg.InferTags.TagSig (seqTagSig)
-- import GHC.StgToCmm.Utils (IPEStats)
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.DFM
-- import GHC.Cmm.Config (CmmConfig)

import Control.Monad.IO.Class (liftIO)

{- *********************************************************************
*                                                                      *
                Initialisation
*                                                                      *
********************************************************************* -}

newCsEnv :: FilePath -> DynFlags -> IO CsEnv
newCsEnv top_dir dflags = newCsEnvWithHUG top_dir dflags (homeUnitId_ dflags) home_unit_graph
  where
    home_unit_graph = unitEnv_singleton
                        (homeUnitId_ dflags)
                        (mkHomeUnitEnv dflags emptyHomePackageTable Nothing)

newCsEnvWithHUG :: FilePath -> DynFlags -> UnitId -> HomeUnitGraph -> IO CsEnv
newCsEnvWithHUG top_dir top_dynflags cur_unit home_unit_graph = do
  nc_var <- initNameCache 'r' knownKeyNames
  fc_var <- initFinderCache
  logger <- initLogger
  tmpfs <- initTmpFs
  let dflags = homeUnitEnv_dflags $ unitEnv_lookup cur_unit home_unit_graph
  unit_env <- initUnitEnv cur_unit home_unit_graph (csNameVersion dflags) (targetPlatform dflags)
  llvm_config <- initLlvmConfigCache top_dir
  return CsEnv { cs_dflags = top_dynflags
               , cs_logger = setLogFlags logger (initLogFlags top_dynflags)
               , cs_targets = []
               , cs_mod_graph = emptyMG
               , cs_NC = nc_var
               , cs_FC = fc_var
               , cs_type_env_vars = emptyKnotVars
               , cs_unit_env = unit_env
               , cs_tmpfs = tmpfs
               , cs_llvm_config = llvm_config
               }

initCsEnv :: Maybe FilePath -> IO CsEnv
initCsEnv mb_top_dir = do
  top_dir <- findTopDir mb_top_dir
  mySettings <- initSysTools top_dir
  dflags <- initDynFlags (defaultDynFlags mySettings)
  cs_env <- newCsEnv top_dir dflags
  setUnsafeGlobalDynFlags dflags
  return cs_env

-- -----------------------------------------------------------------------------

logDiagnostics :: Messages CsMessage -> Cs ()
logDiagnostics w = Cs $ \_ w0 -> return ((), w0 `unionMessages` w)

handleWarningsThrowErrors :: (Messages PsWarning, Messages PsError) -> Cs a
handleWarningsThrowErrors (warnings, errors) = do
  diag_opts <- initDiagOpts <$> getDynFlags
  logDiagnostics (CsPsMessage <$> warnings)
  logger <- getLogger
  let (wWarns, wErrs) = partitionMessages warnings
  liftIO $ printMessages logger NoDiagnosticOpts diag_opts wWarns
  throwErrors $ fmap CsPsMessage $ errors `unionMessages` wErrs

-- -----------------------------------------------------------------------------
-- | parse a file, returning the abstract syntax

csParse' :: ModSummary -> Cs CsParsedModule
csParse' mod_summary
  | Just r <- ms_parsed_mod mod_summary = return r
  | otherwise = do
      dflags <- getDynFlags
      logger <- getLogger
      withTiming logger
        (text "Parser" <+> brackets (ppr $ ms_mod mod_summary))
        (const ()) $
        do
          let src_filename = ms_cs_file mod_summary
              maybe_src_buf = ms_cs_buf mod_summary
          buf <- case maybe_src_buf of
                   Just b -> return b
                   Nothing -> liftIO $ hGetStringBuffer src_filename
          let loc = mkRealSrcLoc (mkFastString src_filename) 1 1

          let diag_opts = initDiagOpts dflags
          when (wopt Opt_WarnUnicodeBidirectionalFormatCharacters dflags) $ do
            case checkBidirectionFormatChars (PsLoc loc (BufPos 0)) buf of
              Nothing -> pure ()
              Just chars@((eloc, chr, _) :| _) ->
                let span = mkSrcSpanPs $ mkPsSpan eloc (advancePsLoc eloc chr)
                in logDiagnostics $ singleMessage $
                     mkPlainMsgEnvelope diag_opts span $
                       CsPsMessage $ PsWarnBidirectionalFormatChars chars

          case unP parseModule (initParserState (initParserOpts dflags) buf loc) of
            PFailed pst ->
              handleWarningsThrowErrors (getPsMessages pst)
            POk pst rdr_module -> do
              liftIO $ putDumpFileMaybe logger Opt_D_dump_parsed "Parser"
                         FormatCSlash (ppr rdr_module)
              liftIO $ putDumpFileMaybe logger Opt_D_dump_parsed_ast "Parser AST"
                         FormatCSlash (showAstData NoBlankSrcSpan
                                                   NoBlankEpAnnotations
                                                   rdr_module)
              liftIO $ putDumpFileMaybe logger Opt_D_source_stats "Source Statistics"
                         FormatText (ppSourceStats False rdr_module)

              let n_cs = FilePath.normalise src_filename
                  TempDir tmp_dir = tmpDir dflags
                  srcs0 = nub $ filter (not . (tmp_dir `isPrefixOf`))
                              $ filter (not . (== n_cs))
                              $ map FilePath.normalise
                              $ filter (not . isPrefixOf "<")
                              $ map unpackFS
                              $ srcfiles pst
                  srcs1 = case ml_cs_file (ms_location mod_summary) of
                            Just f -> filter (/= FilePath.normalise f) srcs0
                            Nothing -> srcs0

              srcs2 <- liftIO $ filterM doesFileExist srcs1

              let res = CsParsedModule
                        { cpm_module = rdr_module
                        , cpm_src_files = srcs2
                        }
                  (warns, errs) = getPsMessages pst

              logDiagnostics (CsPsMessage <$> warns)
              unless (isEmptyMessages errs) $ throwErrors (CsPsMessage <$> errs)

              return res
              

checkBidirectionFormatChars :: PsLoc -> StringBuffer -> Maybe (NonEmpty (PsLoc, Char, String))
checkBidirectionFormatChars start_loc sb
  | containsBidirectionalFormatChar sb = Just $ go start_loc sb
  | otherwise = Nothing
  where
    go :: PsLoc -> StringBuffer -> NonEmpty (PsLoc, Char, String)
    go loc sb
      | atEnd sb = panic "checkBidirectionFormatChars: no char found"
      | otherwise = case nextChar sb of
          (chr, sb)
            | Just desc <- lookup chr bidirectionalFormatChars ->
                (loc, chr, desc) :| go1 (advancePsLoc loc chr) sb
            | otherwise -> go (advancePsLoc loc chr) sb
    go1 :: PsLoc -> StringBuffer -> [(PsLoc, Char, String)]
    go1 loc sb
      | atEnd sb = []
      | otherwise = case nextChar sb of
          (chr, sb)
            | Just desc <- lookup chr bidirectionalFormatChars ->
                (loc, chr, desc) : go1 (advancePsLoc loc chr) sb
            | otherwise -> go1 (advancePsLoc loc chr) sb

-- -----------------------------------------------------------------------------
-- Rename and typecheck a module

csTypecheckAndGetWarnings :: CsEnv -> ModSummary -> IO (FrontendResult, WarningMessages)
csTypecheckAndGetWarnings cs_env summary = runCs' cs_env $
  FrontendTypecheck . fst <$> cs_typecheck False summary Nothing
  
cs_typecheck :: Bool -> ModSummary -> Maybe CsParsedModule -> Cs (TcGblEnv, RenamedStuff)
cs_typecheck keep_rn mod_summary mb_rdr_module = panic "cs_typecheck"

{- *********************************************************************
*                                                                      *
                The main compiler pipeline
*                                                                      *
********************************************************************* -}

type Messager = CsEnv -> (Int, Int) -> RecompileRequired -> ModuleGraphNode -> IO ()

csRecompStatus
  :: Maybe Messager
  -> CsEnv
  -> ModSummary
  -> Maybe ModIface
  -> HomeModLinkable
  -> (Int, Int)
  -> IO CsRecompStatus
csRecompStatus mCsMessage cs_env mod_summary mb_old_iface old_linkable mod_index = do
  let msg what = case mCsMessage of
                   Just csMessage -> csMessage cs_env mod_index what (ModuleNode [] mod_summary)
                   Nothing -> return ()

  recomp_if_result
    <- {-# SCC "checkOldIface" #-}
    liftIO $ checkOldIface cs_env mod_summary mb_old_iface

  case recomp_if_result of
    OutOfDateItem reason mb_checked_iface -> do
      msg $ NeedsRecompile reason
      return $ CsRecompNeeded $ fmap (mi_iface_hash . mi_final_exts) mb_checked_iface

    UpToDateItem checked_iface ->
      let lcl_dflags = ms_cs_opts mod_summary
      in if not (backendGeneratesCode (backend lcl_dflags))
         then do msg UpToDate
                 return $ CsUpToDate checked_iface emptyHomeModInfoLinkable
         else do obj_linkable <- liftIO $
                   checkObjects lcl_dflags (homeMod_object old_linkable) mod_summary
                 trace_if (cs_logger cs_env) (vcat [text "Object Linkable", ppr obj_linkable])

                 let just_o = justObjects <$> obj_linkable
                     recomp_linkable_result =
                       if backendWritesFiles (backend lcl_dflags)
                       then just_o
                       else pprPanic "csRecompStatus" (text $ show $ backend lcl_dflags)

                 case recomp_linkable_result of
                   UpToDateItem linkable -> do
                     msg $ UpToDate
                     return $ CsUpToDate checked_iface $ linkable
                   OutOfDateItem reason _ -> do
                     msg $ NeedsRecompile reason
                     return $ CsRecompNeeded $ Just $ mi_iface_hash $ mi_final_exts checked_iface
                                                   
checkObjects :: DynFlags -> Maybe Linkable -> ModSummary -> IO (MaybeValidated Linkable)
checkObjects dflags mb_old_linkable summary = 
  let dt_enabled = gopt Opt_BuildDynamicToo dflags
      this_mod = ms_mod summary
      mb_obj_date = ms_obj_date summary
      mb_dyn_obj_date = ms_dyn_obj_date summary
      mb_if_date = ms_iface_date summary
      obj_fn = ml_obj_file (ms_location summary)

      checkDynamicObj k = if dt_enabled
        then case (>=) <$> mb_dyn_obj_date <*> mb_if_date of
               Just True -> k
               _ -> return $ outOfDateItemBecause MissingDynObjectFile Nothing
        else k

  in checkDynamicObj $
     case (,) <$> mb_obj_date <*> mb_if_date of
       Just (obj_date, if_date)
         | obj_date >= if_date
           -> case mb_old_linkable of
                Just old_linkable
                  | isObjectLinkable old_linkable
                  , linkableTime old_linkable == obj_date
                    -> return $ UpToDateItem old_linkable
                _ -> UpToDateItem <$> findObjectLinkable this_mod obj_fn obj_date
       _ -> return $ outOfDateItemBecause MissingObjectFile Nothing             
                       
--------------------------------------------------------------
-- Compilers
--------------------------------------------------------------

csDesugarAndSimplify
  :: ModSummary
  -> FrontendResult
  -> Messages CsMessage
  -> Maybe Fingerprint
  -> Cs CsBackendAction
csDesugarAndSimplify summary (FrontendTypecheck tc_result) tc_warnings mb_old_hash = do
  panic "csDesugarAndSimplify"

--------------------------------------------------------------
-- NoRecomp handlers
--------------------------------------------------------------

--------------------------------------------------------------
-- Progress displayers.
--------------------------------------------------------------

oneShotMsg :: Logger -> RecompileRequired -> IO ()
oneShotMsg logger recomp =
  case recomp of
    UpToDate -> compilationProgressMsg logger $ text "compilation IS NOT required"
    NeedsRecompile _ -> return ()
