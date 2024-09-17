module CSlash.HandleEncoding (configureHandleEncoding) where

import GHC.IO.Encoding (textEncodingName)
import System.Environment
import System.IO

configureHandleEncoding :: IO ()
configureHandleEncoding = do
  mb_val <- lookupEnv "CSL_CHARENC"
  case mb_val of
    Just "UTF-8" -> do
      hSetEncoding stdout utf8
      hSetEncoding stderr utf8
    _ -> do
      hSetTranslit stdout
      hSetTranslit stderr

hSetTranslit :: Handle -> IO ()
hSetTranslit h = do
  menc <- hGetEncoding h
  case fmap textEncodingName menc of
    Just name | '/' `notElem` name -> do
                  enc' <- mkTextEncoding $ name ++ "//TRANSLIT"
                  hSetEncoding h enc'
    _ -> return ()
