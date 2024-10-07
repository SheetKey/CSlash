module CSlash.Parser.Header where

import CSlash.Data.Bag

import CSlash.Driver.Errors.Types

import CSlash.Parser.Errors.Types
import CSlash.Parser           ( parseHeader )
import CSlash.Parser.Lexer

import CSlash.Cs
import CSlash.Unit.Module
import CSlash.Builtin.Names

import CSlash.Types.Error
import CSlash.Types.SrcLoc
import CSlash.Types.SourceError
import CSlash.Types.SourceText
import CSlash.Types.PkgQual

import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Monad
import CSlash.Utils.Error
import CSlash.Utils.Exception as Exception

import CSlash.Data.StringBuffer
import CSlash.Data.Maybe
import CSlash.Data.FastString
import qualified CSlash.Data.Strict as Strict

import Control.Monad
import System.IO
import System.IO.Unsafe
import Data.List (partition)
import Data.Char (isSpace)
import Text.ParserCombinators.ReadP (readP_to_S, gather)
import Text.ParserCombinators.ReadPrec (readPrec_to_P)
import Text.Read (readPrec)

--------------------------------------------------------------
-- Get options

getOptionsFromFile :: ParserOpts -> FilePath -> IO (Messages PsMessage, [Located String])
getOptionsFromFile opts filename
  = Exception.bracket
    (openBinaryFile filename ReadMode)
    (hClose)
    (\handle -> do
        (warns, opts) <- fmap (getOptions' opts) (lazyGetToks opts' filename handle)
        seqList opts
          $ seqList (bagToList $ getMessages warns)
          $ return (warns, opts))
  where
    opts' = opts

blockSize :: Int
blockSize = 1024

lazyGetToks :: ParserOpts -> FilePath -> Handle -> IO [Located Token]
lazyGetToks popts filename handle = do
    buf <- hGetStringBufferBlock handle blockSize
    let prag_state = initPragState popts buf loc
    unsafeInterleaveIO $ lazyLexBuf handle prag_state False blockSize
  where
    loc = mkRealSrcLoc (mkFastString filename) 1 1

    lazyLexBuf :: Handle -> PState -> Bool -> Int -> IO [Located Token]
    lazyLexBuf handle state eof size =
      case unP (lexer False return) state of
        POk state' t -> 
          if atEnd (buffer state') && not eof
          then getMore handle state size
          else case unLoc t of
                 ITeof -> return [t]
                 _ -> do rest <- lazyLexBuf handle state' eof size
                         return (t : rest)
        _ | not eof -> getMore handle state size
          | otherwise -> return [L (mkSrcSpanPs (last_loc state)) ITeof]

    getMore :: Handle -> PState -> Int -> IO [Located Token]
    getMore handle state size = do
      let new_size = size * 2
      nextbuf <- hGetStringBufferBlock handle new_size
      if (len nextbuf == 0)
        then lazyLexBuf handle state True new_size
        else do newbuf <- appendStringBuffers (buffer state) nextbuf
                unsafeInterleaveIO $ lazyLexBuf handle state{ buffer = newbuf } False new_size
        
getToks :: ParserOpts -> FilePath -> StringBuffer -> [Located Token]
getToks popts filename buf = lexAll pstate
  where
    pstate = initPragState popts buf loc
    loc = mkRealSrcLoc (mkFastString filename) 1 1

    lexAll state = case unP (lexer False return) state of
                     POk _ t@(L _ ITeof) -> [t]
                     POk state' t -> t : lexAll state'
                     _ -> [L (mkSrcSpanPs (last_loc state)) ITeof]

getOptions' :: ParserOpts -> [Located Token] -> (Messages PsMessage, [Located String])
getOptions' opts toks = parseToks toks
  where
    parseToks _ = (unionManyMessages [], [])
