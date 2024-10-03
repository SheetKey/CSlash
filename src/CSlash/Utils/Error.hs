{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns    #-}

module CSlash.Utils.Error (
  Validity'(..), Validity, andValid, allValid, getInvalids,
  Severity(..),

  Diagnostic(..),
  MsgEnvelope(..),
  MessageClass(..),
  SDoc,
  DecoratedSDoc(unDecorated),
  Messages,
  mkMessages, unionMessages,
  errorsFound, isEmptyMessages,

  pprMessageBag, pprMsgEnvelopeBagWithLoc, pprMsgEnvelopeBagWithLocDefault,
  pprMessages,
  pprLocMsgEnvelope, pprLocMsgEnvelopeDefault,
  formatBulleted,

  DiagOpts (..), emptyDiagOpts, diag_wopt, diag_fatal_wopt,
  emptyMessages, mkDecorated, mkLocMessage,
  mkMsgEnvelope, mkPlainMsgEnvelope, mkPlainErrorMsgEnvelope,
  mkErrorMsgEnvelope,
  mkMCDiagnostic, errorDiagnostic, diagReasonSeverity,

  mkPlainError,
  mkPlainDiagnostic,
  mkDecoratedError,
  mkDecoratedDiagnostic,
  noHints,

  getCaretDiagnostic,

  putMsg, printInfoForUser, printOutputForUser,
  logInfo, logOutput,
  errorMsg,
  fatalErrorMsg,
  compilationProgressMsg,
  showPass,
  withTiming, withTimingSilent,
  debugTraceMsg,
  csExit,
  prettyPrintCsErrors,
  traceCmd,
  traceSystoolCommand,

  sortMsgBag
  ) where

import Prelude hiding ((<>))

import CSlash.Driver.Flags

import CSlash.Data.Bag
import qualified CSlash.Data.EnumSet as EnumSet
import CSlash.Data.EnumSet (EnumSet)

import CSlash.Utils.Exception
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Logger
import CSlash.Types.Error
import CSlash.Types.SrcLoc as SrcLoc
import CSlash.Unit.Module.Warnings

import System.Exit      ( ExitCode(..), exitWith )
import Data.List        ( sortBy )
import Data.Function
import Debug.Trace
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Catch as MC (handle)
import CSlash.Conc ( getAllocationCounter )
import System.CPUTime
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE

data DiagOpts = DiagOpts
  { diag_warning_flags       :: !(EnumSet WarningFlag)
  , diag_fatal_warning_flags :: !(EnumSet WarningFlag)
  , diag_custom_warning_categories       :: !WarningCategorySet
  , diag_fatal_custom_warning_categories :: !WarningCategorySet
  , diag_warn_is_error       :: !Bool
  , diag_reverse_errors      :: !Bool
  , diag_max_errors          :: !(Maybe Int)
  , diag_ppr_ctx             :: !SDocContext
  }

emptyDiagOpts :: DiagOpts
emptyDiagOpts =
    DiagOpts
        { diag_warning_flags = EnumSet.empty
        , diag_fatal_warning_flags = EnumSet.empty
        , diag_custom_warning_categories = emptyWarningCategorySet
        , diag_fatal_custom_warning_categories = emptyWarningCategorySet
        , diag_warn_is_error = False
        , diag_reverse_errors = False
        , diag_max_errors = Nothing
        , diag_ppr_ctx = defaultSDocContext
        }

diag_wopt :: WarningFlag -> DiagOpts -> Bool
diag_wopt wflag opts = wflag `EnumSet.member` diag_warning_flags opts

diag_fatal_wopt :: WarningFlag -> DiagOpts -> Bool
diag_fatal_wopt wflag opts = wflag `EnumSet.member` diag_fatal_warning_flags opts

diag_wopt_custom :: WarningCategory -> DiagOpts -> Bool
diag_wopt_custom wflag opts = wflag `elemWarningCategorySet` diag_custom_warning_categories opts

diag_fatal_wopt_custom :: WarningCategory -> DiagOpts -> Bool
diag_fatal_wopt_custom wflag opts = wflag `elemWarningCategorySet` diag_fatal_custom_warning_categories opts

diagReasonSeverity :: DiagOpts -> DiagnosticReason -> Severity
diagReasonSeverity opts reason = fst (diag_reason_severity opts reason)

diag_reason_severity :: DiagOpts -> DiagnosticReason -> (Severity, ResolvedDiagnosticReason)
diag_reason_severity opts reason = fmap ResolvedDiagnosticReason $ case reason of
  WarningWithFlags wflags -> case wflags' of
    []     -> (SevIgnore, reason)
    w : ws -> case wflagsE of
      []     -> (SevWarning, WarningWithFlags (w :| ws))
      e : es -> (SevError, WarningWithFlags (e :| es))
    where
      wflags' = NE.filter (\wflag -> diag_wopt wflag opts) wflags
      wflagsE = filter (\wflag -> diag_fatal_wopt wflag opts) wflags'

  WarningWithCategory wcat
    | not (diag_wopt_custom wcat opts) -> (SevIgnore, reason)
    | diag_fatal_wopt_custom wcat opts -> (SevError, reason)
    | otherwise                        -> (SevWarning, reason)
  WarningWithoutFlag
    | diag_warn_is_error opts -> (SevError, reason)
    | otherwise             -> (SevWarning, reason)
  ErrorWithoutFlag
    -> (SevError, reason)

mkMCDiagnostic :: DiagOpts -> DiagnosticReason -> Maybe DiagnosticCode -> MessageClass
mkMCDiagnostic opts reason code = MCDiagnostic sev reason' code
  where
    (sev, reason') = diag_reason_severity opts reason

errorDiagnostic :: MessageClass
errorDiagnostic = MCDiagnostic SevError (ResolvedDiagnosticReason ErrorWithoutFlag) Nothing

mk_msg_envelope
  :: Diagnostic e
  => Severity
  -> SrcSpan
  -> NamePprCtx
  -> ResolvedDiagnosticReason
  -> e
  -> MsgEnvelope e
mk_msg_envelope severity locn name_ppr_ctx reason err
 = MsgEnvelope { errMsgSpan = locn
               , errMsgContext = name_ppr_ctx
               , errMsgDiagnostic = err
               , errMsgSeverity = severity
               , errMsgReason = reason
               }

mkMsgEnvelope
  :: Diagnostic e
  => DiagOpts
  -> SrcSpan
  -> NamePprCtx
  -> e
  -> MsgEnvelope e
mkMsgEnvelope opts locn name_ppr_ctx err
 = mk_msg_envelope sev locn name_ppr_ctx reason err
  where
    (sev, reason) = diag_reason_severity opts (diagnosticReason err)

mkErrorMsgEnvelope :: Diagnostic e
                   => SrcSpan
                   -> NamePprCtx
                   -> e
                   -> MsgEnvelope e
mkErrorMsgEnvelope locn name_ppr_ctx msg =
 assert (diagnosticReason msg == ErrorWithoutFlag) $ mk_msg_envelope SevError locn name_ppr_ctx (ResolvedDiagnosticReason ErrorWithoutFlag) msg

mkPlainMsgEnvelope :: Diagnostic e
                   => DiagOpts
                   -> SrcSpan
                   -> e
                   -> MsgEnvelope e
mkPlainMsgEnvelope opts locn msg =
  mkMsgEnvelope opts locn alwaysQualify msg

mkPlainErrorMsgEnvelope :: Diagnostic e
                        => SrcSpan
                        -> e
                        -> MsgEnvelope e
mkPlainErrorMsgEnvelope locn msg =
  mk_msg_envelope SevError locn alwaysQualify (ResolvedDiagnosticReason ErrorWithoutFlag) msg

data Validity' a
  = IsValid
  | NotValid a
  deriving Functor

type Validity = Validity' SDoc

andValid :: Validity' a -> Validity' a -> Validity' a
andValid IsValid v = v
andValid v _       = v

allValid :: [Validity' a] -> Validity' a
allValid []       = IsValid
allValid (v : vs) = v `andValid` allValid vs

getInvalids :: [Validity' a] -> [a]
getInvalids vs = [d | NotValid d <- vs]

formatBulleted :: DecoratedSDoc -> SDoc
formatBulleted (unDecorated -> docs)
  = sdocWithContext $ \ctx -> case msgs ctx of
        []    -> Outputable.empty
        [msg] -> msg
        xs    -> vcat $ map starred xs
    where
    msgs ctx = filter (not . Outputable.isEmpty ctx) docs
    starred = (bullet<+>)

pprMessages :: Diagnostic e => DiagnosticOpts e -> Messages e -> SDoc
pprMessages e = vcat . pprMsgEnvelopeBagWithLoc e . getMessages

pprMsgEnvelopeBagWithLoc :: Diagnostic e => DiagnosticOpts e -> Bag (MsgEnvelope e) -> [SDoc]
pprMsgEnvelopeBagWithLoc e bag = [ pprLocMsgEnvelope e item | item <- sortMsgBag Nothing bag ]

pprMsgEnvelopeBagWithLocDefault :: forall e . Diagnostic e => Bag (MsgEnvelope e) -> [SDoc]
pprMsgEnvelopeBagWithLocDefault bag = [ pprLocMsgEnvelopeDefault item | item <- sortMsgBag Nothing bag ]

pprLocMsgEnvelopeDefault :: forall e . Diagnostic e => MsgEnvelope e -> SDoc
pprLocMsgEnvelopeDefault = pprLocMsgEnvelope (defaultDiagnosticOpts @e)

pprLocMsgEnvelope :: Diagnostic e => DiagnosticOpts e -> MsgEnvelope e -> SDoc
pprLocMsgEnvelope opts (MsgEnvelope { errMsgSpan      = s
                               , errMsgDiagnostic = e
                               , errMsgSeverity  = sev
                               , errMsgContext   = name_ppr_ctx
                               , errMsgReason    = reason })
  = withErrStyle name_ppr_ctx $
      mkLocMessage
        (MCDiagnostic sev reason (diagnosticCode e))
        s
        (formatBulleted $ diagnosticMessage opts e)

sortMsgBag :: Maybe DiagOpts -> Bag (MsgEnvelope e) -> [MsgEnvelope e]
sortMsgBag mopts = maybeLimit . sortBy (cmp `on` errMsgSpan) . bagToList
  where
    cmp
      | Just opts <- mopts
      , diag_reverse_errors opts
      = SrcLoc.rightmost_smallest
      | otherwise
      = SrcLoc.leftmost_smallest
    maybeLimit
      | Just opts <- mopts
      , Just err_limit <- diag_max_errors opts
      = take err_limit
      | otherwise
      = id

csExit :: Logger -> Int -> IO ()
csExit logger val
  | val == 0  = exitWith ExitSuccess
  | otherwise = do errorMsg logger (text "\nCompilation had errors\n\n")
                   exitWith (ExitFailure val)

errorMsg :: Logger -> SDoc -> IO ()
errorMsg logger msg
   = logMsg logger errorDiagnostic noSrcSpan $
     withPprStyle defaultErrStyle msg

fatalErrorMsg :: Logger -> SDoc -> IO ()
fatalErrorMsg logger msg =
    logMsg logger MCFatal noSrcSpan $ withPprStyle defaultErrStyle msg

compilationProgressMsg :: Logger -> SDoc -> IO ()
compilationProgressMsg logger msg = do
  let logflags = logFlags logger
  let str = renderWithContext (log_default_user_context logflags) (text "CSL progress: " <> msg)
  traceEventIO str
  when (logVerbAtLeast logger 1) $
    logOutput logger $ withPprStyle defaultUserStyle msg

showPass :: Logger -> String -> IO ()
showPass logger what =
  when (logVerbAtLeast logger 2) $
    logInfo logger $ withPprStyle defaultUserStyle (text "***" <+> text what <> colon)

data PrintTimings = PrintTimings | DontPrintTimings
  deriving (Eq, Show)

withTiming :: MonadIO m
           => Logger
           -> SDoc         
           -> (a -> ())    
           -> m a
           -> m a
withTiming logger what force action =
  withTiming' logger what force PrintTimings action

withTimingSilent
  :: MonadIO m
  => Logger
  -> SDoc
  -> (a -> ())
  -> m a      
  -> m a
withTimingSilent logger what force action =
  withTiming' logger what force DontPrintTimings action

withTiming' :: MonadIO m
            => Logger
            -> SDoc         
            -> (a -> ())    
            -> PrintTimings 
            -> m a          
            -> m a
withTiming' logger what force_result prtimings action
  = if logVerbAtLeast logger 2 --  || logHasDumpFlag logger Opt_D_dump_timings
    then do when printTimingsNotDumpToFile $ liftIO $
              logInfo logger $ withPprStyle defaultUserStyle $
                text "***" <+> what <> colon
            let ctx = log_default_user_context (logFlags logger)
            alloc0 <- liftIO getAllocationCounter
            start <- liftIO getCPUTime
            eventBegins ctx what
            recordAllocs alloc0
            !r <- action
            () <- pure $ force_result r
            eventEnds ctx what
            end <- liftIO getCPUTime
            alloc1 <- liftIO getAllocationCounter
            recordAllocs alloc1
            -- recall that allocation counter counts down
            let alloc = alloc0 - alloc1
                time = realToFrac (end - start) * 1e-9

            when (logVerbAtLeast logger 2 && printTimingsNotDumpToFile)
                $ liftIO $ logInfo logger $ withPprStyle defaultUserStyle
                    (text "!!!" <+> what <> colon <+> text "finished in"
                     <+> doublePrec 2 time
                     <+> text "milliseconds"
                     <> comma
                     <+> text "allocated"
                     <+> doublePrec 3 (realToFrac alloc / 1024 / 1024)
                     <+> text "megabytes")

            -- whenPrintTimings $
            --     putDumpFileMaybe logger Opt_D_dump_timings "" FormatText
            --         $ text $ showSDocOneLine ctx
            --         $ hsep [ what <> colon
            --                , text "alloc=" <> ppr alloc
            --                , text "time=" <> doublePrec 3 time
            --                ]
            pure r
     else action

    where whenPrintTimings =
            liftIO . when printTimings

          printTimings =
            prtimings == PrintTimings

          -- Avoid both printing to console and dumping to a file (#20316).
          printTimingsNotDumpToFile =
            printTimings
            && not (log_dump_to_file (logFlags logger))

          recordAllocs alloc =
            liftIO $ traceMarkerIO $ "CSL:allocs:" ++ show alloc

          eventBegins ctx w = do
            let doc = eventBeginsDoc ctx w
            whenPrintTimings $ traceMarkerIO doc
            liftIO $ traceEventIO doc

          eventEnds ctx w = do
            let doc = eventEndsDoc ctx w
            whenPrintTimings $ traceMarkerIO doc
            liftIO $ traceEventIO doc

          eventBeginsDoc ctx w = showSDocOneLine ctx $ text "CSL:started:" <+> w
          eventEndsDoc   ctx w = showSDocOneLine ctx $ text "CSL:finished:" <+> w

debugTraceMsg :: Logger -> Int -> SDoc -> IO ()
debugTraceMsg logger val msg =
   when (log_verbosity (logFlags logger) >= val) $
      logInfo logger (withPprStyle defaultDumpStyle msg)
{-# INLINE debugTraceMsg #-}  

putMsg :: Logger -> SDoc -> IO ()
putMsg logger msg = logInfo logger (withPprStyle defaultUserStyle msg)

printInfoForUser :: Logger -> NamePprCtx -> SDoc -> IO ()
printInfoForUser logger name_ppr_ctx msg
  = logInfo logger (withUserStyle name_ppr_ctx AllTheWay msg)

printOutputForUser :: Logger -> NamePprCtx -> SDoc -> IO ()
printOutputForUser logger name_ppr_ctx msg
  = logOutput logger (withUserStyle name_ppr_ctx AllTheWay msg)

logInfo :: Logger -> SDoc -> IO ()
logInfo logger msg = logMsg logger MCInfo noSrcSpan msg

logOutput :: Logger -> SDoc -> IO ()
logOutput logger msg = logMsg logger MCOutput noSrcSpan msg


prettyPrintCsErrors :: ExceptionMonad m => Logger -> m a -> m a
prettyPrintCsErrors logger = do
  let ctx = log_default_user_context (logFlags logger)
  MC.handle $ \e -> case e of
    PprPanic str doc ->
        pprDebugAndThen ctx panic (text str) doc
    PprSorry str doc ->
        pprDebugAndThen ctx sorry (text str) doc
    PprProgramError str doc ->
        pprDebugAndThen ctx pgmError (text str) doc
    _ -> liftIO $ throwIO e

traceCmd :: Logger -> String -> String -> IO a -> IO a
traceCmd logger phase_name cmd_line action = do
  showPass logger phase_name
  let
    cmd_doc = text cmd_line
    handle_exn exn = do
      debugTraceMsg logger 2 (char '\n')
      debugTraceMsg logger 2 (text "Failed:" <+> cmd_doc <+> text (show exn))
      throwCsExceptionIO (ProgramError (show exn))
  debugTraceMsg logger 3 cmd_doc
  loggerTraceFlush logger
   -- And run it!
  action `catchIO` handle_exn

traceSystoolCommand :: Logger -> String -> IO a -> IO a
traceSystoolCommand logger tool = withTiming logger (text "systool:" <> text tool) (const ())
