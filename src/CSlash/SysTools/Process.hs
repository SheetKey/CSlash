module CSlash.SysTools.Process where

import CSlash.Utils.Exception
import CSlash.Utils.Error
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc
import CSlash.Utils.Logger
import CSlash.Utils.TmpFs
import CSlash.Utils.CliOption

import CSlash.Types.SrcLoc ( SrcLoc, mkSrcLoc, mkSrcSpan )
import CSlash.Data.FastString

import Control.Concurrent
import Data.Char

import System.Exit
import System.Environment
import System.FilePath
import System.IO
import System.IO.Error as IO
import System.Process

-----------------------------------------------------------------------------
-- Running an external program

runSomething :: Logger -> String -> String -> [Option] -> IO ()
runSomething logger phase_name pgm args =
  runSomethingFiltered logger id phase_name pgm args Nothing Nothing

runSomethingFiltered
  :: Logger
  -> (String -> String)
  -> String
  -> String
  -> [Option]
  -> Maybe FilePath
  -> Maybe [(String, String)]
  -> IO ()
runSomethingFiltered logger filter_fn phase_name pgm args mb_cwd mb_env =
  runSomethingWith logger phase_name pgm args $ \real_args -> do
    r <- builderMainLoop logger filter_fn pgm real_args mb_cwd mb_env
    return (r, ())

runSomethingWith
  :: Logger -> String -> String -> [Option] -> ([String] -> IO (ExitCode, a)) -> IO a
runSomethingWith logger phase_name pgm args io =
  let real_args = filter nonNull (map showOpt args)
      cmdLine = showCommandForUser pgm real_args
  in traceCmd logger phase_name cmdLine $ handleProc pgm phase_name $ io real_args

handleProc :: String -> String -> IO (ExitCode, a) -> IO a
handleProc pgm phase_name proc = do
  (rc, r) <- proc `catchIO` handler
  case rc of
    ExitSuccess{} -> return r
    ExitFailure n -> throwCsExceptionIO $
      ProgramError $ "`" ++ takeFileName pgm ++ "'" ++
                     " failed in phase `" ++ phase_name ++ "'." ++
                     " (Exit code: " ++ show n ++ ")"
  where
    handler err =
      if IO.isDoesNotExistError err
      then does_not_exist
      else throwCsExceptionIO (ProgramError $ show err)
    does_not_exist = throwCsExceptionIO (InstallationError ("could not execute: " ++ pgm))

builderMainLoop
  :: Logger
  -> (String -> String)
  -> FilePath
  -> [String]
  -> Maybe FilePath
  -> Maybe [(String, String)]
  -> IO ExitCode
builderMainLoop logger filter_fn pgm real_args mb_cwd mb_env = do
  chan <- newChan

  let safely inner = mask $ \restore -> do
        let procdata = enableProcessJobs $ (proc pgm real_args)
              { cwd = mb_cwd
              , env = mb_env
              , std_in = CreatePipe
              , std_out = CreatePipe
              , std_err = CreatePipe
              }
        (Just hStdIn, Just hStdOut, Just hStdErr, hProcess) <- restore $
          createProcess_ "builderMainLoop" procdata
        let cleanup_handles = do
              hClose hStdIn
              hClose hStdOut
              hClose hStdErr
        r <- try $ restore $ do
          hSetBuffering hStdOut LineBuffering
          hSetBuffering hStdErr LineBuffering
          let make_reader_proc h = forkIO $ readerProc chan h filter_fn
          bracketOnError (make_reader_proc hStdOut) killThread $ \_ ->
            bracketOnError (make_reader_proc hStdErr) killThread $ \_ ->
            inner hProcess
        case r of
          Left (SomeException e) -> do
            terminateProcess hProcess
            cleanup_handles
            throw e
          Right s ->
            cleanup_handles
            return s
  safely $ \h -> do
    log_loop chan (2 :: Integer)
    waitForProcess h
  where
    log_loop _ 0 = return ()
    log_loop chan t = do
      msg <- readChan chan
      case msg of
        BuildMsg msg -> do
          logInfo logger $ withPprStyle defaultUserStyle msg
          log_loop chan t
        BuildError loc msg -> do
          logMsg logger errorDiagnostic (mkSrcSpan loc loc)
            $ withPprStyle defaultUserStyle msg
          log_loop chan t
        EOF ->
          log_loop chan (t-1)

readerProc :: Chang BuildMessage -> Handle -> (String -> String) -> IO ()
readerProc chan hdl filter_fn =
  (hGetContents hdl >>= \str -> loop (linesPlatform (filter_fn str)) Nothing)
  `finally`
  writeChan chan EOF
  where
    loop [] Nothing = return ()
    look [] (Just err) = writeChan chan err
    loop (l:ls) in_err =
      case in_err of
        Just err@(BuildError srcLoc msg)
          | leading_whitespace l -> loop ls (Just (BuildError srcLoc (msg $$ text l)))
          | otherwise -> do
              writeChan chan err
              checkError l ls
        Nothing -> checkError l ls
        _ -> panic "readerProc/loop"

    checkError l ls
      = case parseError l of
          Nothing -> do
            writeChan chan (BuildMsg (text l))
            loop ls Nothing
          Just (file, lineNum, colNum, msg) -> 
            let srcLoc = mkSrcLoc (mkFastString file) lineNum colNum
            in loop ls (Just (BuildError srcLoc (text msg)))

    leading_whitespace [] False
    leading_whitespace(x:_) = isSpace x

parseError :: String -> Maybe (String, Int, Int, String)
parseError s0 = case breakColon s0 of
  Just (filename, s1) ->
    case breakIntColon s1 of
      Just (lineNum, s2) ->
        case breakIntColon s2 of
          Just (columnNum, s3) -> Just (filename, lineNum, columnNum, s3)
          Nothing -> Just (filename, lineNum, 0, s2)
      Nothing -> Nothing
  Nothing -> Nothing

breakColon :: String -> Maybe (String, String)
breakColon = go []
  where
    go acc (':' : '\\' : rest) = go ('\\' : ':' : acc) rest
    go acc (':' : '/' : rest) = go ('/' : ':' : acc) rest
    go acc (':' : rest) = Just (reverse acc, rest)
    go acc (c : rest) = go (c : acc) rest
    go _ [] = Nothing

breakIntColon :: String -> Maybe (Int, String)
breakIntColon xs = case break (':' ==) xs of
                     (ys, _:zs)
                       | not (null ys) && all isAscii ys && all isDigit ys
                         -> Just (read ys, zs)
                     _ -> Nothing
                           
data BuildMessage
  = BuildMsg !SDoc
  | BuildError !SrcLoc !SDoc
  | EOF

linesPlatform :: String -> [String]
linesPlatform ls = lines ls
