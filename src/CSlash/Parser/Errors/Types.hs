{-# LANGUAGE DeriveGeneric #-}

module CSlash.Parser.Errors.Types where

-- base
import Data.List.NonEmpty

-- compiler
import CSlash.Data.FastString

import CSlash.Cs.Extension

import CSlash.Types.Error
import CSlash.Types.Name.Reader
import CSlash.Types.Name.Occurrence
import CSlash.Types.SrcLoc

import CSlash.Parser.Errors.Basic
import CSlash.Parser.Types
import CSlash.Parser.Annotation

import CSlash.Language.Syntax.Expr
import CSlash.Language.Syntax.Type
import CSlash.Language.Syntax.Pat

-- ghc
import GHC.Generics (Generic)

type PsWarning = PsMessage
type PsError = PsMessage

data PsMessage
  = PsUnknownMessage (UnknownDiagnostic (DiagnosticOpts PsMessage))
  | PsWarnBidirectionalFormatChars (NonEmpty (PsLoc, Char, String))
  | PsWarnTab !Word
  | PsWarnOperatorWhitespace !FastString !OperatorWhitespaceOccurrence
  | PsErrEmptyLambda
  | PsErrEmptyTyLam
  | PsErrEmptyTyLamTy
  | PsErrMissingBlock
  | PsErrLexer !LexErr !LexErrKind
  | PsErrParse !String !PsErrParseDetails
  | PsErrUnexpectedQualifiedConstructor !RdrName
  | PsErrTupleSectionInPat
  | PsErrOpFewArgs !RdrName
  | PsErrImportQualifiedTwice
  | PsErrImportPreQualified
  | PsErrVarForTyCon !RdrName
  | PsErrPrecedenceOutOfRange !Int
  | PsErrIfInPat -- replaces PsErrIfThenElseInPat
  | PsErrLambdaInPat 
  | PsErrTyLambdaInPat 
  | PsErrCaseInPat
  | PsErrLetInPat
  | PsErrArrowExprInPat !(CsExpr Ps)
  | PsErrInvalidInfixHole
  | PsErrSemiColonsInCondExpr !(CsExpr Ps) !Bool (CsExpr Ps) !Bool !(CsExpr Ps)
  | PsErrAtInPatPos
  | PsErrUnexpectedAsPat
  | PsErrCaseInFunAppExpr !(LCsExpr Ps)
  | PsErrLambdaInFunAppExpr !(LCsExpr Ps)
  | PsErrLetInFunAppExpr !(LCsExpr Ps)
  | PsErrIfInFunAppExpr !(LCsExpr Ps)
  | PsErrMalformedTyDecl !(LocatedN RdrName)
  | PsErrParseErrorOnInput !OccName
  | PsErrInvalidTypeSignature !PsInvalidTypeSignature !(LCsExpr Ps)
  | PsErrUnexpectedTypeInDecl !(LCsType Ps)
                              !SDoc
                              !RdrName
                              [LCsTypeArg Ps]
                              !SDoc
  | PsErrInPat !(PatBuilder Ps) !PsErrInPatDetails
  | PsErrInTyPat !(CsType Ps)
  | PsErrUnicodeCharLooksLike Char Char String
  | PsErrParseRightOpSectionInPat !RdrName !(PatBuilder Ps)
  | PsErrInvalidKindRelation !RdrName
  deriving Generic

data PsErrParseDetails = PsErrParseDetails

data PsInvalidTypeSignature
  = PsErrInvalidTypeSig_Qualified
  | PsErrInvalidTypeSig_DataCon
  | PsErrInvalidTypeSig_Other

data PatIsRecursive
  = YesPatIsRecursive
  | NoPatIsRecursive

data ParseContext = ParseContext
  { is_infix :: !(Maybe RdrName)
  }
  deriving (Eq)

data PsErrInPatDetails
  = PEIP_NegApp
  | PEIP_TypeArgs [CsConPatTyArg Ps]
  | PEIP_RecPattern [LPat Ps]
                    !PatIsRecursive
                    !ParseContext
  | PEIP_OtherPatDetails !ParseContext

noParseContext :: ParseContext
noParseContext = ParseContext Nothing

fromParseContext :: ParseContext -> PsErrInPatDetails
fromParseContext = PEIP_OtherPatDetails

data LexErrKind
  = LexErrKind_EOF
  | LexErrKind_UTF8
  | LexErrKind_Char !Char
  deriving (Show, Eq, Ord)

data LexErr
  = LexError
  | LexNumEscapeRange
  | LexStringCharLit
  | LexStringCharLitEOF
  | LexUnterminatedComment
