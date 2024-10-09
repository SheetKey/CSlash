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

------------------------------------------------------------------------------
-- Parse the imports of a source file.

getImports
  :: ParserOpts
  -> Bool
  -> StringBuffer
  -> FilePath
  -> FilePath
  -> IO (Either
         (Messages PsMessage)
         ( [(RawPkgQual, Located ModuleName)]
         , Bool
         , Located ModuleName ))         
getImports popts implicit_prelude buf filename source_filename = do
  let loc = mkRealSrcLoc (mkFastString filename) 1 1
  case unP parseHeader (initParserState popts buf loc) of
    PFailed pst -> return $ Left $ getPsErrorMessages pst
    POk pst rdr_module -> fmap Right $ 
      let (_, errs) = getPsMessages pst
      in if not (isEmptyMessages errs)
         then throwErrors (CsPsMessage <$> errs)
         else let csmod = unLoc rdr_module
                  mod = csmodName csmod
                  imps = csmodImports csmod
                  ord_idecls = imps

                  (ordinary_imps, csl_prim_import)
                    = partition ((/= moduleName cSLASH_PRIM) . unLoc . ideclName . unLoc)
                      ord_idecls

                  pre_loc = srcLocSpan (mkSrcLoc (mkFastString source_filename) 1 1)
                  implicit_imports = mkPrelImports (unLoc mod) pre_loc implicit_prelude imps
                  convImport (L _ i) = (NoRawPkgQual, reLoc $ ideclName i)
              in return ( map convImport (implicit_imports ++ ordinary_imps)
                        , not (null csl_prim_import)
                        , reLoc mod )
                                 
mkPrelImports :: ModuleName -> SrcSpan -> Bool -> [LImportDecl Ps] -> [LImportDecl Ps]
mkPrelImports this_mod loc implicit_prelude import_decls
  | this_mod == pRELUDE_NAME
    || explicit_prelude_import
    || not implicit_prelude
  = []
  | otherwise
  = [preludeImportDecl]
  where
    explicit_prelude_import = any is_prelude_import import_decls

    is_prelude_import (L _ decl) =
      unLoc (ideclName decl) == pRELUDE_NAME
      -- && case ideclPkgQual decl of
      --      NoRawPkgQual -> True
      --      RawPkgQual b -> sl_fs b == unitIdFS baseUnitId

    loc' = noAnnSrcSpan loc

    preludeImportDecl :: LImportDecl Ps
    preludeImportDecl = L loc' $ ImportDecl
      { ideclExt = XImportDeclPass
                   { ideclAnn = noAnn
                   , ideclSourceText = NoSourceText
                   , ideclImplicit = True
                   }
      , ideclName = L loc' pRELUDE_NAME
      -- , ideclPkgQual = NoRawPkgQual
      , ideclQualified = NotQualified
      , ideclAs = Nothing
      , ideclImportList = Nothing
      }
                     

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

-----------------------------------------------------------------------------
-- Complain about non-dynamic flags in OPTIONS pragmas.

checkProcessArgsResult :: MonadIO m => [Located String] -> m ()
checkProcessArgsResult flags
  = when (notNull flags) $
    liftIO $ throwErrors $ foldMap (singleMessage . mkMsg) flags
  where
    mkMsg (L loc flag)
      = mkPlainErrorMsgEnvelope loc $
        CsPsMessage $ PsHeaderMessage $ PsErrUnknownOptionsPragma flag
