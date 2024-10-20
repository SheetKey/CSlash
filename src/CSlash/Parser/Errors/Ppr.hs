{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module CSlash.Parser.Errors.Ppr where

import Prelude hiding ((<>))

import CSlash.Driver.Flags
import CSlash.Data.FastString
import CSlash.Cs.Expr
import CSlash.Types.Error
import CSlash.Types.SrcLoc
import CSlash.Types.Error.Codes
import CSlash.Types.Hint.Ppr (perhapsAsPat)
import CSlash.Types.Name.Reader (opIsAt, rdrNameOcc)
import CSlash.Types.Name.Occurrence (isSymOcc, occNameFS, varName)
import CSlash.Parser.Errors.Basic
import CSlash.Parser.Errors.Types
import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Builtin.Names (allNameStringList)

import Data.List.NonEmpty (NonEmpty((:|)))

instance Diagnostic PsMessage where
  type DiagnosticOpts PsMessage = NoDiagnosticOpts
  diagnosticMessage opts = \case
    PsUnknownMessage (UnknownDiagnostic f m)
      -> diagnosticMessage (f opts) m
    PsHeaderMessage m -> psHeaderMessageDiagnostic m
    PsWarnBidirectionalFormatChars ((loc, _, desc) :| xs)
      -> mkSimpleDecorated $
            text "A unicode bidirectional formatting character" <+> parens (text desc)
         $$ text "was found at offset" <+> ppr (bufPos (psBufPos loc))
            <+> text "in the file"
         $$ (case xs of
           [] -> empty
           xs -> text "along with further bidirectional formatting characters at"
                 <+> pprChars xs
            where
              pprChars [] = empty
              pprChars ((loc,_,desc):xs) = text "offset"
                                           <+> ppr (bufPos (psBufPos loc))
                                           <> text ":" <+> text desc
                                       $$ pprChars xs
              )
         $$ text "Bidirectional formatting characters may be rendered misleadingly in certain editors"
    PsWarnTab tc
      -> mkSimpleDecorated $
           text "Tab character found here"
             <> (if tc == 1
                 then text ""
                 else text ", and in" <+> speakNOf (fromIntegral (tc - 1)) (text "further location"))
             <> text "."
    PsWarnOperatorWhitespace sym occ_type
      -> let mk_msg occ_type_str =
                  text "The" <+> text occ_type_str <+> text "use of a" <+> quotes (ftext sym)
                    <+> text "might be repurposed as special syntax"
               $$ nest 2 (text "by a future language extension.")
         in mkSimpleDecorated $
         case occ_type of
           OperatorWhitespaceOccurrence_Prefix -> mk_msg "prefix"
           OperatorWhitespaceOccurrence_Suffix -> mk_msg "suffix"
           OperatorWhitespaceOccurrence_TightInfix -> mk_msg "tight infix"
    PsErrEmptyLambda
      -> mkSimpleDecorated $ text "A lambda requires at least on parameter"
    PsErrMissingBlock
      -> mkSimpleDecorated $ text "Missing block"
    PsErrLexer err kind
      -> mkSimpleDecorated $ hcat
           [ case err of
              LexError               -> text "lexical error"
              LexNumEscapeRange      -> text "numeric escape sequence out of range"
              LexStringCharLit       -> text "lexical error in string/character literal"
              LexStringCharLitEOF    -> text "unexpected end-of-file in string/character literal"
              LexUnterminatedComment -> text "unterminated `{-'"
           , case kind of
              LexErrKind_EOF    -> text " at end of input"
              LexErrKind_UTF8   -> text " (UTF-8 decoding error)"
              LexErrKind_Char c -> text $ " at character " ++ show c
           ]      
    PsErrParse token _details
      | null token
      -> mkSimpleDecorated $ text "parse error (possibly incorrect indentation or mismatched brackets)"
      | otherwise
      -> mkSimpleDecorated $ text "parse error on input" <+> quotes (text token)
    PsErrUnexpectedQualifiedConstructor v
      -> mkSimpleDecorated $
           hang (text "Expected an unqualified type constructor:") 2
                (ppr v)
    PsErrTupleSectionInPat
      -> mkSimpleDecorated $ text "Tuple section in pattern context"
    PsErrOpFewArgs op
      -> mkSimpleDecorated $
           text "Operator applied to too few arguments:" <+> ppr op
    PsErrImportQualifiedTwice
      -> mkSimpleDecorated $ text "Multiple occurrences of 'qualified'"
    PsErrImportPreQualified
      -> mkSimpleDecorated $
            text "Found" <+> quotes (text "qualified")
             <+> text "in prepositive position"
    PsErrVarForTyCon name
      -> mkSimpleDecorated $
           text "Expecting a type constructor but found a variable,"
             <+> quotes (ppr name) <> text "."
           $$ if isSymOcc $ rdrNameOcc name
              then text "If" <+> quotes (ppr name) <+> text "is a type constructor"
                    <+> text "then enable ExplicitNamespaces and use the 'type' keyword."
              else empty
    PsErrPrecedenceOutOfRange i
      -> mkSimpleDecorated $ text "Precedence out of range: " <> int i
    PsErrTypeInExpr ty
      -> mkSimpleDecorated $
         text "Unexpected type" <+> quotes (ppr ty) <+> text "in an expression."
    PsErrKindInExpr kd
      -> mkSimpleDecorated $
         text "Unexpected kind" <+> quotes (ppr kd) <+> text "in an expression."
    PsErrExpInType e
      -> mkSimpleDecorated $
         text "Unexpected expression" <+> quotes (ppr e) <+> text "in a type."
    PsErrKindInType kd
      -> mkSimpleDecorated $
         text "Unexpected kind" <+> quotes (ppr kd) <+> text "in a type."
    PsErrNegAppInType
      -> mkSimpleDecorated $ text "Invalid neg app in type."
    PsErrLetInType
      -> mkSimpleDecorated $ text "(let ... in ...)-syntax in type"
    PsErrTyLamInType
      -> mkSimpleDecorated $ text "(/\\ ...)-syntax in type"
    PsErrCaseInType
      -> mkSimpleDecorated $ text "(case ... of ...)-syntax in type"
    PsErrInBracesType
      -> mkSimpleDecorated $ text "({ ... })-syntax in type"
    PsErrSumDCType
      -> mkSimpleDecorated $ text "Invalid sum data constructor in type."
    PsErrExpInKind e
      -> mkSimpleDecorated $
         text "Unexpected expression" <+> quotes (ppr e) <+> text "in a kind."
    PsErrTypeInKind ty
      -> mkSimpleDecorated $
         text "Unexpected type" <+> quotes (ppr ty) <+> text "in a kind."
    PsErrKindWithSig
      -> mkSimpleDecorated $ text "Invalid kind with signature."
    PsErrKindOpApp
      -> mkSimpleDecorated $ text "Invalid kind operator application."
    PsErrKindApp
      -> mkSimpleDecorated $ text "Invalid kind application."
    PsErrNegAppInKind
      -> mkSimpleDecorated $ text "Invalid neg app in kind."
    PsErrLetInKind
      -> mkSimpleDecorated $ text "(let ... in ...)-syntax in kind"
    PsErrLamInKind
      -> mkSimpleDecorated $ text "(\\ ...)-syntax in kind"
    PsErrTyLamInKind
      -> mkSimpleDecorated $ text "(/\\ ...)-syntax in kind"
    PsErrCaseInKind
      -> mkSimpleDecorated $ text "(case ... of ...)-syntax in kind"
    PsErrKindCon
      -> mkSimpleDecorated $ text "Invalid kind constructor."
    PsErrLitInKind
      -> mkSimpleDecorated $ text "Invalid literal in kind."
    PsErrOverLitInKind
      -> mkSimpleDecorated $ text "Invalid literal in kind."
    PsErrSumOrTupleKind
      -> mkSimpleDecorated $ text "Invalid sum or tuple in kind."
    PsErrWildCardKind
      -> mkSimpleDecorated $ text "Invalid wildcard in kind."
    PsErrInBracesKind
      -> mkSimpleDecorated $ text "({ ... })-syntax in kind"
    PsErrKindSection
      -> mkSimpleDecorated $ text "Invalid section in kind."
    PsErrTypeInPat ty
      -> mkSimpleDecorated $ parse_error_in_pat <+>
         text "Unexpected type" <+> quotes (ppr ty) <+> text "in a pattern."
    PsErrKindInPat kd
      -> mkSimpleDecorated $ parse_error_in_pat <+>
         text "Unexpected kind" <+> quotes (ppr kd) <+> text "in a pattern."
    PsErrIfInPat
      -> mkSimpleDecorated $ text "(if ...) in pattern"
    PsErrIfInType
      -> mkSimpleDecorated $ text "(if ...) in type"
    PsErrIfInKind
      -> mkSimpleDecorated $ text "(if ...) in kind"
    PsErrLambdaInPat
      -> mkSimpleDecorated $ text "Illegal lambda-syntax in pattern"
    PsErrCaseInPat
      -> mkSimpleDecorated $ text "(case ... of ...)-syntax in pattern"
    PsErrLetInPat
      -> mkSimpleDecorated $ text "(let ... in ...)-syntax in pattern"
    PsErrInvalidInfixHole
      -> mkSimpleDecorated $ text "Invalid infix hole, expected an infix operator"
    PsErrCaseInFunAppExpr a
      -> mkSimpleDecorated $ pp_unexpected_fun_app (text "case expression") a
    PsErrLambdaInFunAppExpr a
      -> mkSimpleDecorated $ pp_unexpected_fun_app (text "lambda expression") a
    PsErrLambdaInTyFunAppExpr t
      -> mkSimpleDecorated $ pp_unexpected_ty_fun_app (text "type lambda expression") t
    PsErrLetInFunAppExpr a
      -> mkSimpleDecorated $ pp_unexpected_fun_app (text "let expression") a
    PsErrIfInFunAppExpr a
      -> mkSimpleDecorated $ pp_unexpected_fun_app (text "if expression") a
    PsErrParseErrorOnInput occ
      -> mkSimpleDecorated $ text "parse error on input" <+> ftext (occNameFS occ)
    PsErrInvalidTypeSignature reason lhs
      -> mkSimpleDecorated $ case reason of
           PsErrInvalidTypeSig_DataCon   -> text "Invalid data constructor" <+> quotes (ppr lhs) <+>
                                            text "in type signature" <> colon $$
                                            text "You can only define data constructors in data type declarations."
           PsErrInvalidTypeSig_Qualified -> text "Invalid qualified name in type signature."
           PsErrInvalidTypeSig_Other     -> text "Invalid type signature" <> colon $$
                                            text "A type signature should be of form" <+>
                                            placeHolder "variables" <+> dcolon <+> placeHolder "type" <>
                                            dot
            where placeHolder = angleBrackets . text
    PsErrUnexpectedTypeInDecl t what tc tparms equals_or_where
       -> mkSimpleDecorated $
            vcat [ text "Unexpected type" <+> quotes (ppr t)
                 , text "In the" <+> what
                   <+> text "declaration for" <+> quotes tc'
                 , vcat[ (text "A" <+> what
                          <+> text "declaration should have form")
                 , nest 2
                   (what
                    <+> tc'
                    <+> hsep (map text (takeList tparms allNameStringList))
                    <+> equals_or_where) ] ]
          where
            tc' = ppr tc
    PsErrInPat s details
      -> let msg  = parse_error_in_pat
             body = case details of
                 PEIP_NegApp -> text "-" <> ppr s
                 PEIP_TypeArgs peipd_tyargs
                   | not (null peipd_tyargs) -> ppr s <+> vcat [
                               hsep (map ppr peipd_tyargs)
                             , text "Type applications in patterns are only allowed on data constructors."
                             ]
                   | otherwise -> ppr s
                 PEIP_OtherPatDetails (ParseContext (Just fun))
                  -> ppr s <+> text "In a function binding for the"
                                     <+> quotes (ppr fun)
                                     <+> text "operator."
                                  $$ if opIsAt fun
                                        then perhapsAsPat
                                        else empty
                 _  -> ppr s
         in mkSimpleDecorated $ msg <+> body
    PsErrInTyPat t details
      -> let msg = parse_error_in_ty_pat
             body = case details of
                      PEIP_NegApp -> text "-" <> ppr t
                      PEIP_TypeArgs peipd_tyargs
                        | not (null peipd_tyargs) -> ppr t <+> vcat 
                          [ hsep (map ppr peipd_tyargs)
                          , text "Type application are not allowed in type patterns."
                          ]
                        | otherwise -> ppr t
                      PEIP_OtherPatDetails (ParseContext (Just fun))
                        -> ppr t <+> text "In a type function binding for the"
                                 <+> quotes (ppr fun)
                                 <+> text "operator."
                      _ -> ppr t
         in mkSimpleDecorated $ msg <+> body
                            
    PsErrUnicodeCharLooksLike bad_char looks_like_char looks_like_char_name
      -> mkSimpleDecorated $
           hsep [ text "Unicode character"
                -- purposefully not using `quotes (text [bad_char])`, because the quotes function adds smart quotes,
                -- and smart quotes may be the topic of this error message
                , text "'" <> text [bad_char] <> text "' (" <> text (show bad_char) <> text ")"
                , text "looks like"
                , text "'" <> text [looks_like_char] <> text "' (" <> text looks_like_char_name <> text ")" <> comma
                , text "but it is not" ]
    _ -> mkSimpleDecorated $ text "diagnosticMessage PsMessage"

  diagnosticReason = \case
    PsUnknownMessage m -> diagnosticReason m
    PsHeaderMessage m -> psHeaderMessageReason m
    PsWarnBidirectionalFormatChars {} ->
      WarningWithFlag Opt_WarnUnicodeBidirectionalFormatCharacters
    PsWarnTab {} -> WarningWithFlag Opt_WarnTabs
    PsWarnOperatorWhitespace sym occ -> WarningWithFlag Opt_WarnOperatorWhitespace
    PsErrEmptyLambda {} -> ErrorWithoutFlag
    PsErrEmptyTyLam {} -> ErrorWithoutFlag
    PsErrEmptyTyLamTy {} -> ErrorWithoutFlag
    PsErrMissingBlock -> ErrorWithoutFlag
    PsErrLexer {} -> ErrorWithoutFlag
    PsErrParse {} -> ErrorWithoutFlag
    PsErrUnexpectedQualifiedConstructor {} -> ErrorWithoutFlag
    PsErrTupleSectionInPat {} -> ErrorWithoutFlag
    PsErrOpFewArgs {} -> ErrorWithoutFlag
    PsErrImportQualifiedTwice -> ErrorWithoutFlag          
    PsErrImportPreQualified -> WarningWithFlag Opt_WarnPrepositiveQualifiedModule            
    PsErrVarForTyCon {} -> ErrorWithoutFlag
    PsErrPrecedenceOutOfRange {} -> ErrorWithoutFlag
    PsErrIfInPat -> ErrorWithoutFlag
    PsErrIfInType -> ErrorWithoutFlag
    PsErrIfInKind -> ErrorWithoutFlag
    PsErrLambdaInPat {} -> ErrorWithoutFlag                   
    PsErrTyLambdaInPat {} -> ErrorWithoutFlag                 
    PsErrCaseInPat -> ErrorWithoutFlag                     
    PsErrLetInPat -> ErrorWithoutFlag                      
    PsErrArrowExprInPat {} -> ErrorWithoutFlag
    PsErrInvalidInfixHole -> ErrorWithoutFlag              
    PsErrSemiColonsInCondExpr {} -> ErrorWithoutFlag
    PsErrAtInPatPos -> ErrorWithoutFlag                    
    PsErrUnexpectedAsPat -> ErrorWithoutFlag               
    PsErrCaseInFunAppExpr {} -> ErrorWithoutFlag
    PsErrLambdaInFunAppExpr {} -> ErrorWithoutFlag
    PsErrLambdaInTyFunAppExpr {} -> ErrorWithoutFlag
    PsErrLetInFunAppExpr {} -> ErrorWithoutFlag
    PsErrIfInFunAppExpr {} -> ErrorWithoutFlag
    PsErrMalformedTyDecl {} -> ErrorWithoutFlag
    PsErrParseErrorOnInput {} -> ErrorWithoutFlag
    PsErrInvalidTypeSignature {} -> ErrorWithoutFlag
    PsErrUnexpectedTypeInDecl {} -> ErrorWithoutFlag
    PsErrInPat {} -> ErrorWithoutFlag
    PsErrInTyPat {} -> ErrorWithoutFlag
    PsErrUnicodeCharLooksLike {} -> ErrorWithoutFlag
    PsErrParseRightOpSectionInPat {} -> ErrorWithoutFlag
    PsErrInvalidKindRelation {} -> ErrorWithoutFlag
    PsErrTypeInExpr {} -> ErrorWithoutFlag
    PsErrKindInExpr {} -> ErrorWithoutFlag
    PsErrExpInType {} -> ErrorWithoutFlag
    PsErrKindInType {} -> ErrorWithoutFlag
    PsErrNegAppInType -> ErrorWithoutFlag
    PsErrLetInType -> ErrorWithoutFlag
    PsErrTyLamInType -> ErrorWithoutFlag
    PsErrCaseInType -> ErrorWithoutFlag
    PsErrLitInType -> ErrorWithoutFlag
    PsErrOverLitInType -> ErrorWithoutFlag
    PsErrInBracesType -> ErrorWithoutFlag
    PsErrSumDCType -> ErrorWithoutFlag
    PsErrExpInKind {} -> ErrorWithoutFlag
    PsErrTypeInKind {} -> ErrorWithoutFlag
    PsErrKindWithSig -> ErrorWithoutFlag
    PsErrKindOpApp -> ErrorWithoutFlag
    PsErrKindApp -> ErrorWithoutFlag
    PsErrNegAppInKind -> ErrorWithoutFlag
    PsErrLetInKind -> ErrorWithoutFlag
    PsErrLamInKind -> ErrorWithoutFlag
    PsErrTyLamInKind -> ErrorWithoutFlag
    PsErrCaseInKind -> ErrorWithoutFlag
    PsErrKindCon -> ErrorWithoutFlag
    PsErrLitInKind -> ErrorWithoutFlag
    PsErrOverLitInKind -> ErrorWithoutFlag
    PsErrSumOrTupleKind -> ErrorWithoutFlag
    PsErrWildCardKind -> ErrorWithoutFlag
    PsErrInBracesKind -> ErrorWithoutFlag
    PsErrKindSection -> ErrorWithoutFlag
    PsErrTypeInPat {} -> ErrorWithoutFlag
    PsErrKindInPat {} -> ErrorWithoutFlag
    PsErrParseLeftOpSectionInPat {} -> ErrorWithoutFlag
    
  diagnosticHints = \case
    PsUnknownMessage m -> diagnosticHints m
    PsHeaderMessage m -> psHeaderMessageHints m
    PsWarnBidirectionalFormatChars {} -> noHints
    PsWarnTab {} -> [SuggestUseSpaces]
    PsWarnOperatorWhitespace sym occ -> [SuggestUseWhitespaceAround (unpackFS sym) occ]
    PsErrEmptyLambda {} -> noHints
    PsErrEmptyTyLam {} -> noHints
    PsErrEmptyTyLamTy {} -> noHints
    PsErrMissingBlock -> noHints
    PsErrLexer {} -> noHints
    PsErrParse {} -> noHints
    PsErrUnexpectedQualifiedConstructor {} -> noHints
    PsErrTupleSectionInPat {} -> noHints             
    PsErrOpFewArgs {} -> noHints
    PsErrImportQualifiedTwice -> noHints          
    PsErrImportPreQualified -> [SuggestQualifiedAfterModuleName]            
    PsErrVarForTyCon {} -> noHints
    PsErrPrecedenceOutOfRange {} -> noHints
    PsErrIfInPat -> noHints
    PsErrIfInType -> noHints
    PsErrIfInKind -> noHints
    PsErrLambdaInPat {} -> noHints                   
    PsErrTyLambdaInPat {} -> noHints
    PsErrCaseInPat -> noHints
    PsErrLetInPat -> noHints
    PsErrArrowExprInPat {} -> noHints
    PsErrInvalidInfixHole -> noHints
    PsErrSemiColonsInCondExpr {} -> noHints
    PsErrAtInPatPos -> noHints
    PsErrUnexpectedAsPat -> noHints
    PsErrCaseInFunAppExpr {} -> [SuggestParentheses]
    PsErrLambdaInFunAppExpr {} -> [SuggestParentheses]
    PsErrLambdaInTyFunAppExpr {} -> [SuggestParentheses]
    PsErrLetInFunAppExpr {} -> [SuggestParentheses]
    PsErrIfInFunAppExpr {} -> [SuggestParentheses]
    PsErrMalformedTyDecl {} -> noHints
    PsErrParseErrorOnInput {} -> noHints
    PsErrInvalidTypeSignature reason lhs ->
      if | PsErrInvalidTypeSig_Qualified <- reason
           -> [SuggestTypeSignatureRemoveQualifier]
         | otherwise -> noHints
    PsErrUnexpectedTypeInDecl {} -> noHints
    PsErrInPat {} -> noHints
    PsErrInTyPat {} -> noHints
    PsErrUnicodeCharLooksLike {} -> noHints
    PsErrParseRightOpSectionInPat {} -> noHints
    PsErrInvalidKindRelation {} -> noHints
    PsErrTypeInExpr {} -> noHints
    PsErrKindInExpr {} -> noHints
    PsErrExpInType {} -> noHints
    PsErrKindInType {} -> noHints
    PsErrNegAppInType -> noHints
    PsErrLetInType -> noHints
    PsErrTyLamInType -> noHints
    PsErrCaseInType -> noHints
    PsErrLitInType -> noHints
    PsErrOverLitInType -> noHints
    PsErrInBracesType -> noHints
    PsErrSumDCType -> noHints
    PsErrExpInKind {} -> noHints
    PsErrTypeInKind {} -> noHints
    PsErrKindWithSig -> noHints
    PsErrKindOpApp -> noHints
    PsErrKindApp -> noHints
    PsErrNegAppInKind -> noHints
    PsErrLetInKind -> noHints
    PsErrLamInKind -> noHints
    PsErrTyLamInKind -> noHints
    PsErrCaseInKind -> noHints
    PsErrKindCon -> noHints
    PsErrLitInKind -> noHints
    PsErrOverLitInKind -> noHints
    PsErrSumOrTupleKind -> noHints
    PsErrWildCardKind -> noHints
    PsErrInBracesKind -> noHints
    PsErrKindSection -> noHints
    PsErrTypeInPat {} -> noHints
    PsErrKindInPat {} -> noHints
    PsErrParseLeftOpSectionInPat {} -> noHints

  diagnosticCode = constructorCode

psHeaderMessageDiagnostic :: PsHeaderMessage -> DecoratedSDoc
psHeaderMessageDiagnostic  = \case
  PsErrUnknownOptionsPragma flag ->
    mkSimpleDecorated $ text "Unknown flag in {-# OPTIONS_CSL #-} pragma:" <+> text flag

psHeaderMessageReason :: PsHeaderMessage -> DiagnosticReason
psHeaderMessageReason = \case
  PsErrUnknownOptionsPragma {} -> ErrorWithoutFlag

psHeaderMessageHints :: PsHeaderMessage -> [CsHint]
psHeaderMessageHints = \case
  PsErrUnknownOptionsPragma {} -> noHints

pp_unexpected_fun_app :: Outputable a => SDoc -> a -> SDoc
pp_unexpected_fun_app e a =
  text "Unexpected " <> e <> text " in function application:"
  $$ nest 4 (ppr a)

pp_unexpected_ty_fun_app :: Outputable a => SDoc -> a -> SDoc
pp_unexpected_ty_fun_app e a =
  text "Unexpected " <> e <> text " in type function application:"
  $$ nest 4 (ppr a)

parse_error_in_pat :: SDoc
parse_error_in_pat = text "Parse error in pattern:"

parse_error_in_ty_pat :: SDoc
parse_error_in_ty_pat = text "Parse error in type pattern:"
