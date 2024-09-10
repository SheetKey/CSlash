module CSlash.Driver.Config.Parser where

import CSlash.Platform

import CSlash.Driver.Session
import CSlash.Driver.Config.Diagnostic

import CSlash.Parser.Lexer

initParserOpts :: DynFlags -> ParserOpts
initParserOpts =
  mkParserOpts
  <$> initDiagOpts
  <*> gopt Opt_KeepRawTokenStream
