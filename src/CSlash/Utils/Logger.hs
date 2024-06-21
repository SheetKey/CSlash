{-# LANGUAGE RankNTypes #-}

module GHC.Utils.Logger
    ( Logger
    , HasLogger (..)
    , ContainsLogger (..)

    , initLogger
    , LogAction
    , LogJsonAction
    , DumpAction
    , TraceAction
    , DumpFormat (..)

    , popLogHook
    , pushLogHook
    , popJsonLogHook
    , pushJsonLogHook
    , popDumpHook
    , pushDumpHook
    , popTraceHook
    , pushTraceHook
    , makeThreadSafe

    , LogFlags (..)
    , defaultLogFlags
    , log_dopt
    , log_set_dopt
    , setLogFlags
    , updateLogFlags
    , logFlags
    , logHasDumpFlag
    , logVerbAtLeast

    , putLogMsg
    , defaultLogAction
    , defaultLogJsonAction
    , defaultLogActionHPrintDoc
    , defaultLogActionHPutStrDoc
    , logMsg
    , logJsonMsg
    , logDumpMsg

    , defaultDumpAction
    , putDumpFile
    , putDumpFileMaybe
    , putDumpFileMaybe'
    , withDumpFileHandle
    , touchDumpFile
    , logDumpFile

    , defaultTraceAction
    , putTraceMsg
    , loggerTraceFlushUpdate
    , loggerTraceFlush
    , logTraceMsg
    )
where

import CSlash.Driver.Flags
import CSlash.Types.Error
import CSlash.Types.SrcLoc

import qualified CSlash.Utils.Ppr as Pretty
import CSlash.Utils.Outputable
import CSlash.Utils.Json
import CSlash.Utils.Panic

import CSlash.Data.EnumSet (EnumSet)
import qualified CSlash.Data.EnumSet as EnumSet
import CSlash.Data.FastString

import System.Directory
import System.FilePath  ( takeDirectory, (</>) )
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.List (stripPrefix)
import Data.Time
import System.IO
import Control.Monad
import Control.Concurrent.MVar
import System.IO.Unsafe
import Debug.Trace (trace)
import GHC.Platform.Ways

data LogFlags = LogFlags
  { log_default_user_context :: SDocContext
  , log_default_dump_context :: SDocContext
  , log_dump_flags           :: !(EnumSet DumpFlag) 
  , log_show_caret           :: !Bool               
  , log_diagnostics_as_json  :: !Bool               
  , log_show_warn_groups     :: !Bool               
  , log_enable_timestamps    :: !Bool               
  , log_dump_to_file         :: !Bool               
  , log_dump_dir             :: !(Maybe FilePath)   
  , log_dump_prefix          :: !FilePath           
  , log_dump_prefix_override :: !(Maybe FilePath)   
  , log_with_ways            :: !Bool               
  , log_enable_debug         :: !Bool               
  , log_verbosity            :: !Int                
  , log_ways                 :: !(Maybe Ways)       
  }

defaultLogFlags :: LogFlags
defaultLogFlags = LogFlags
  { log_default_user_context = defaultSDocContext
  , log_default_dump_context = defaultSDocContext
  , log_dump_flags           = EnumSet.empty
  , log_show_caret           = True
  , log_diagnostics_as_json  = False
  , log_show_warn_groups     = True
  , log_enable_timestamps    = True
  , log_dump_to_file         = False
  , log_dump_dir             = Nothing
  , log_dump_prefix          = ""
  , log_dump_prefix_override = Nothing
  , log_with_ways           = True
  , log_enable_debug         = False
  , log_verbosity            = 0
  , log_ways                 = Nothing
  }

log_dopt :: DumpFlag -> LogFlags -> Bool
log_dopt = getDumpFlagFrom log_verbosity log_dump_flags

log_set_dopt :: DumpFlag -> LogFlags -> LogFlags
log_set_dopt f logflags = logflags { log_dump_flags = EnumSet.insert f (log_dump_flags logflags) }

logHasDumpFlag :: Logger -> DumpFlag -> Bool
logHasDumpFlag logger f = log_dopt f (logFlags logger)

logVerbAtLeast :: Logger -> Int -> Bool
logVerbAtLeast logger v = log_verbosity (logFlags logger) >= v

updateLogFlags :: Logger -> (LogFlags -> LogFlags) -> Logger
updateLogFlags logger f = setLogFlags logger (f (logFlags logger))

setLogFlags :: Logger -> LogFlags -> Logger
setLogFlags logger flags = logger { logFlags = flags }

type LogAction = LogFlags
              -> MessageClass
              -> SrcSpan
              -> SDoc
              -> IO ()

type LogJsonAction = LogFlags
                   -> MessageClass
                   -> JsonDoc
                   -> IO ()

type DumpAction = LogFlags
               -> PprStyle
               -> DumpFlag
               -> String
               -> DumpFormat
               -> SDoc
               -> IO ()

type TraceAction a = LogFlags -> String -> SDoc -> a -> a

data DumpFormat
   = FormatCSlash
   | FormatByteCode
   | FormatLLVM
   | FormatText
   deriving (Show,Eq)

type DumpCache = MVar (Map FilePath (MVar ()))

data Logger = Logger
    { log_hook   :: [LogAction -> LogAction]
    , json_log_hook :: [LogJsonAction -> LogJsonAction]
    , dump_hook  :: [DumpAction -> DumpAction]
    , trace_hook :: forall a. [TraceAction a -> TraceAction a]
    , generated_dumps :: DumpCache
    , trace_flush :: IO ()
    , logFlags :: !LogFlags
    }

loggerTraceFlushUpdate :: Logger -> (IO () -> IO ()) -> Logger
loggerTraceFlushUpdate logger upd = logger { trace_flush = upd (trace_flush logger) }

loggerTraceFlush :: Logger -> IO ()
loggerTraceFlush logger = trace_flush logger

defaultTraceFlush :: IO ()
defaultTraceFlush = hFlush stderr

initLogger :: IO Logger
initLogger = do
    dumps <- newMVar Map.empty
    return $ Logger
        { log_hook        = []
        , json_log_hook   = []
        , dump_hook       = []
        , trace_hook      = []
        , generated_dumps = dumps
        , trace_flush     = defaultTraceFlush
        , logFlags        = defaultLogFlags
        }

putLogMsg :: Logger -> LogAction
putLogMsg logger = foldr ($) defaultLogAction (log_hook logger)

putJsonLogMsg :: Logger -> LogJsonAction
putJsonLogMsg logger = foldr ($) defaultLogJsonAction (json_log_hook logger)

putDumpFile :: Logger -> DumpAction
putDumpFile logger =
    let
        fallback = putLogMsg logger
        dumps    = generated_dumps logger
        deflt    = defaultDumpAction dumps fallback
    in foldr ($) deflt (dump_hook logger)

putTraceMsg :: Logger -> TraceAction a
putTraceMsg logger = foldr ($) defaultTraceAction (trace_hook logger)

pushLogHook :: (LogAction -> LogAction) -> Logger -> Logger
pushLogHook h logger = logger { log_hook = h:log_hook logger }

popLogHook :: Logger -> Logger
popLogHook logger = case log_hook logger of
    []   -> panic "popLogHook: empty hook stack"
    _:hs -> logger { log_hook = hs }

pushJsonLogHook :: (LogJsonAction -> LogJsonAction) -> Logger -> Logger
pushJsonLogHook h logger = logger { json_log_hook = h:json_log_hook logger }

popJsonLogHook :: Logger -> Logger
popJsonLogHook logger = case json_log_hook logger of
    []   -> panic "popJsonLogHook: empty hook stack"
    _:hs -> logger { json_log_hook = hs}

pushDumpHook :: (DumpAction -> DumpAction) -> Logger -> Logger
pushDumpHook h logger = logger { dump_hook = h:dump_hook logger }

popDumpHook :: Logger -> Logger
popDumpHook logger = case dump_hook logger of
    []   -> panic "popDumpHook: empty hook stack"
    _:hs -> logger { dump_hook = hs }

pushTraceHook :: (forall a. TraceAction a -> TraceAction a) -> Logger -> Logger
pushTraceHook h logger = logger { trace_hook = h:trace_hook logger }

popTraceHook :: Logger -> Logger
popTraceHook logger = case trace_hook logger of
    [] -> panic "popTraceHook: empty hook stack"
    _  -> logger { trace_hook = tail (trace_hook logger) }

makeThreadSafe :: Logger -> IO Logger
makeThreadSafe logger = do
    lock <- newMVar ()
    let
        with_lock :: forall a. IO a -> IO a
        with_lock act = withMVar lock (const act)

        log action logflags msg_class loc doc =
            with_lock (action logflags msg_class loc doc)

        dmp action logflags sty opts str fmt doc =
            with_lock (action logflags sty opts str fmt doc)

        trc :: forall a. TraceAction a -> TraceAction a
        trc action logflags str doc v =
            unsafePerformIO (with_lock (return $! action logflags str doc v))

    return $ pushLogHook log
           $ pushDumpHook dmp
           $ pushTraceHook trc
           $ logger

defaultLogJsonAction :: LogJsonAction
defaultLogJsonAction logflags msg_class jsdoc =
  case msg_class of
      MCOutput                     -> printOut msg
      MCDump                       -> printOut (msg $$ blankLine)
      MCInteractive                -> putStrSDoc msg
      MCInfo                       -> printErrs msg
      MCFatal                      -> printErrs msg
      MCDiagnostic SevIgnore _ _   -> pure () -- suppress the message
      MCDiagnostic _sev _rea _code -> printErrs msg
  where
    printOut   = defaultLogActionHPrintDoc  logflags False stdout
    printErrs  = defaultLogActionHPrintDoc  logflags False stderr
    putStrSDoc = defaultLogActionHPutStrDoc logflags False stdout
    msg = renderJSON jsdoc

jsonLogAction :: LogAction
jsonLogAction _ (MCDiagnostic SevIgnore _ _) _ _ = return () -- suppress the message
jsonLogAction logflags msg_class srcSpan msg
  =
    defaultLogActionHPutStrDoc logflags True stdout
      (withPprStyle PprCode (doc $$ text ""))
    where
      str = renderWithContext (log_default_user_context logflags) msg
      doc = renderJSON $
              JSObject [ ( "span", spanToDumpJSON srcSpan )
                       , ( "doc" , JSString str )
                       , ( "messageClass", json msg_class )
                       ]
      spanToDumpJSON :: SrcSpan -> JsonDoc
      spanToDumpJSON s = case s of
                 (RealSrcSpan rss _) -> JSObject [ ("file", json file)
                                                , ("startLine", json $ srcSpanStartLine rss)
                                                , ("startCol", json $ srcSpanStartCol rss)
                                                , ("endLine", json $ srcSpanEndLine rss)
                                                , ("endCol", json $ srcSpanEndCol rss)
                                                ]
                   where file = unpackFS $ srcSpanFile rss
                 UnhelpfulSpan _ -> JSNull

defaultLogAction :: LogAction
defaultLogAction logflags msg_class srcSpan msg
  | log_dopt Opt_D_dump_json logflags = jsonLogAction logflags msg_class srcSpan msg
  | otherwise = case msg_class of
      MCOutput                     -> printOut msg
      MCDump                       -> printOut (msg $$ blankLine)
      MCInteractive                -> putStrSDoc msg
      MCInfo                       -> printErrs msg
      MCFatal                      -> printErrs msg
      MCDiagnostic SevIgnore _ _   -> pure () -- suppress the message
      MCDiagnostic _sev _rea _code -> printDiagnostics
    where
      printOut   = defaultLogActionHPrintDoc  logflags False stdout
      printErrs  = defaultLogActionHPrintDoc  logflags False stderr
      putStrSDoc = defaultLogActionHPutStrDoc logflags False stdout
      message = mkLocMessageWarningGroups (log_show_warn_groups logflags) msg_class srcSpan msg

      printDiagnostics = do
        caretDiagnostic <-
            if log_show_caret logflags
            then getCaretDiagnostic msg_class srcSpan
            else pure empty
        printErrs $ getPprStyle $ \style ->
          withPprStyle (setStyleColoured True style)
            (message $+$ caretDiagnostic $+$ blankLine)

defaultLogActionHPrintDoc :: LogFlags -> Bool -> Handle -> SDoc -> IO ()
defaultLogActionHPrintDoc logflags asciiSpace h d
 = defaultLogActionHPutStrDoc logflags asciiSpace h (d $$ text "")

defaultLogActionHPutStrDoc :: LogFlags -> Bool -> Handle -> SDoc -> IO ()
defaultLogActionHPutStrDoc logflags asciiSpace h d
  = printSDoc (log_default_user_context logflags) (Pretty.PageMode asciiSpace) h d

defaultDumpAction :: DumpCache -> LogAction -> DumpAction
defaultDumpAction dumps log_action logflags sty flag title _fmt doc =
  dumpSDocWithStyle dumps log_action sty logflags flag title doc

dumpSDocWithStyle :: DumpCache -> LogAction -> PprStyle -> LogFlags -> DumpFlag -> String -> SDoc -> IO ()
dumpSDocWithStyle dumps log_action sty logflags flag hdr doc =
    withDumpFileHandle dumps logflags flag writeDump
  where
    writeDump (Just handle) = do
        doc' <- if null hdr
                then return doc
                else do timeStamp <- if log_enable_timestamps logflags
                          then (text . show) <$> getCurrentTime
                          else pure empty
                        let d = timeStamp
                                $$ blankLine
                                $$ doc
                        return $ mkDumpDoc hdr d
        defaultLogActionHPrintDoc logflags True handle (withPprStyle sty doc')

    writeDump Nothing = do
        let (doc', msg_class)
              | null hdr  = (doc, MCOutput)
              | otherwise = (mkDumpDoc hdr doc, MCDump)
        log_action logflags msg_class noSrcSpan (withPprStyle sty doc')

withDumpFileHandle :: DumpCache -> LogFlags -> DumpFlag -> (Maybe Handle -> IO ()) -> IO ()
withDumpFileHandle dumps logflags flag action = do
    let dump_ways = log_ways logflags
    let mFile = chooseDumpFile logflags dump_ways flag
    case mFile of
      Just fileName -> do
        lock <- modifyMVar dumps $ \gd ->
            case Map.lookup fileName gd of
              Nothing -> do
                  lock <- newMVar ()
                  let gd' = Map.insert fileName lock gd
                  createDirectoryIfMissing True (takeDirectory fileName)
                  writeFile fileName ""
                  return (gd', lock)
              Just lock -> do
                  return (gd, lock)

        let withLock k = withMVar lock $ \() -> k >> return ()
        withLock $ withFile fileName AppendMode $ \handle -> do
            hSetEncoding handle utf8

            action (Just handle)
      Nothing -> action Nothing

chooseDumpFile :: LogFlags -> Maybe Ways -> DumpFlag -> Maybe FilePath
chooseDumpFile logflags ways flag
    | log_dump_to_file logflags || forced_to_file
    = Just $ setDir (getPrefix ++ way_infix ++ dump_suffix)

    | otherwise
    = Nothing
  where
    way_infix = case ways of
      _ | not (log_with_ways logflags) -> ""
      Nothing -> ""
      Just ws
        | null ws || null (waysTag ws) -> ""
        | otherwise -> waysTag ws ++ "."
    (forced_to_file, dump_suffix) = case flag of
        Opt_D_th_dec_file -> (True, "th.hs")
        _                 -> (False, default_suffix)

    default_suffix = map (\c -> if c == '_' then '-' else c) $
      let str = show flag
      in case stripPrefix "Opt_D_" str of
        Just x  -> x
        Nothing -> panic ("chooseDumpFile: bad flag name: " ++ str)

    getPrefix
       | Just prefix <- log_dump_prefix_override logflags
          = prefix
       | otherwise
          = log_dump_prefix logflags
    setDir f = case log_dump_dir logflags of
                 Just d  -> d </> f
                 Nothing ->       f

defaultTraceAction :: TraceAction a
defaultTraceAction logflags title doc x =
  if not (log_enable_debug logflags)
    then x
    else trace (renderWithContext (log_default_dump_context logflags)
                             (sep [text title, nest 2 doc])) x

logMsg :: Logger -> MessageClass -> SrcSpan -> SDoc -> IO ()
logMsg logger mc loc msg = putLogMsg logger (logFlags logger) mc loc msg

logJsonMsg :: ToJson a => Logger -> MessageClass -> a -> IO ()
logJsonMsg logger mc d = putJsonLogMsg logger (logFlags logger) mc  (json d)

logDumpFile :: Logger -> PprStyle -> DumpFlag -> String -> DumpFormat -> SDoc -> IO ()
logDumpFile logger = putDumpFile logger (logFlags logger)

logTraceMsg :: Logger -> String -> SDoc -> a -> a
logTraceMsg logger hdr doc a = putTraceMsg logger (logFlags logger) hdr doc a

logDumpMsg :: Logger -> String -> SDoc -> IO ()
logDumpMsg logger hdr doc = logMsg logger MCDump noSrcSpan
  (withPprStyle defaultDumpStyle
  (mkDumpDoc hdr doc))

mkDumpDoc :: String -> SDoc -> SDoc
mkDumpDoc hdr doc
   = vcat [blankLine,
           line <+> text hdr <+> line,
           doc,
           blankLine]
     where
        line = text "===================="

putDumpFileMaybe :: Logger -> DumpFlag -> String -> DumpFormat -> SDoc -> IO ()
putDumpFileMaybe logger = putDumpFileMaybe' logger alwaysQualify
{-# INLINE putDumpFileMaybe #-}

putDumpFileMaybe'
    :: Logger
    -> NamePprCtx
    -> DumpFlag
    -> String
    -> DumpFormat
    -> SDoc
    -> IO ()
putDumpFileMaybe' logger name_ppr_ctx flag hdr fmt doc
  = when (logHasDumpFlag logger flag) $
    logDumpFile' logger name_ppr_ctx flag hdr fmt doc
{-# INLINE putDumpFileMaybe' #-}  


logDumpFile' :: Logger -> NamePprCtx -> DumpFlag
             -> String -> DumpFormat -> SDoc -> IO ()
{-# NOINLINE logDumpFile' #-}
logDumpFile' logger name_ppr_ctx flag hdr fmt doc
  = logDumpFile logger (mkDumpStyle name_ppr_ctx) flag hdr fmt doc

touchDumpFile :: Logger -> DumpFlag -> IO ()
touchDumpFile logger flag =
    withDumpFileHandle (generated_dumps logger) (logFlags logger) flag (const (return ()))

class HasLogger m where
    getLogger :: m Logger

class ContainsLogger t where
    extractLogger :: t -> Logger
