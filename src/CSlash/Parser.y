{
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
  
module CSlash.Parser
  ( parseModule--, parseImport
  --, parseDeclaration, parseExpression
  --, parseTypeSignature
  --, parseType
  , parseHeader
  ) where

-- base
import Control.Monad (unless, liftM, when, (<=<))
import GHC.Exts
import Data.Maybe (maybeToList)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
-- import qualified Prelude -- for happy-generated code
-- import Prelude (Maybe(..), Either(..))

import CSlash.Cs

import CSlash.Unit.Module
import CSlash.Unit.Module.Warnings

import CSlash.Data.OrdList
import CSlash.Data.FastString
import CSlash.Data.Maybe (orElse)

import CSlash.Utils.Outputable
import CSlash.Utils.Error
import CSlash.Utils.Misc (looksLikePackageName, fstOf3, sndOf3, thdOf3)
import CSlash.Utils.Panic
import qualified CSlash.Data.Strict as Strict

import CSlash.Types.Name.Reader
import CSlash.Types.Name.Occurrence
  (varName, tcClsName, tvName, kvName, occNameFS, mkVarOccFS, isConOccFS, NameSpace(UNKNOWN_NS))
import CSlash.Types.SrcLoc
import CSlash.Types.Basic
import CSlash.Types.Error (CsHint(..))
import CSlash.Types.Fixity
import CSlash.Types.SourceText
import CSlash.Types.PkgQual

import CSlash.Core.DataCon (DataCon, dataConName)

import CSlash.Parser.PostProcess
import CSlash.Parser.Lexer
import CSlash.Parser.Annotation
import CSlash.Parser.Errors.Types
import CSlash.Parser.Errors.Ppr ()

import CSlash.Builtin.Types (sumTyCon, tupleDataCon, unitDataCon)
import CSlash.Builtin.Types.Prim (fUNTyCon, unrestrictedFUNTyCon, affineFUNTyCon, linearFUNTyCon)

import qualified Data.Semigroup as Semi
}

%expect 0 -- shift/reduce conflicts

%token
  'as' { L _ ITas }
  'case' { L _ ITcase }
  'else' { L _ ITelse }
  'hiding' { L _ IThiding }
  'if' { L _ ITif }
  'import' { L _ ITimport }
  'in' { L _ ITin }
  'infix' { L _ ITinfix }
  'infixl' { L _ ITinfixl }
  'infixr' { L _ ITinfixr }
  'let' { L _ ITlet }
  'module' { L _ ITmodule }
  'of' { L _ ITof }
  'qualified' { L _ ITqualified }
  'then' { L _ ITthen }
  'type' { L _ ITtype }
  'where' { L _ ITwhere }

  'forall' { L _ ITforall }

  ':' { L _ ITcolon }
  '=' { L _ ITequal }
  '\\' { L _ ITlam }
  '|' { L _ ITvbar }
  '<-' { L _ ITlarrow }
  '->' { L _ ITrarrow }
  '=>' { L _ ITdarrow }
  ARR_U { L _ ITarrowU }
  ARR_A { L _ ITarrowA }
  ARR_L { L _ ITarrowL }
  ARR_K { L _ (ITarrowK _) }
  PREFIX_MINUS { L _ ITprefixminus }
  SUFFIX_ARR { L _ ITsuffixarr }
  TIGHT_INFIX_AT { L _ ITtightinfixat }
  U_KIND { L _ ITstar }
  A_KIND { L _ ITbullet }
  L_KIND { L _ ITcirc }
  '.' { L _ ITdot }

  '/\\' { L _ ITbiglam }

  OPEN_LAYOUT { L _ ITolayout }
  CLOSE_LAYOUT { L _ ITclayout }
  ';' { L _ ITnewlinelayout }

  '{' { L _ ITocurly }
  '}' { L _ ITccurly }
  '(' { L _ IToparen }
  ')' { L _ ITcparen }
  ',' { L _ ITcomma }
  '_' { L _ ITunderscore }
  '`' { L _ ITbackquote }

  VARID { L _ (ITvarid _) }
  CONID { L _ (ITconid _) }
  VARSYM { L _ (ITvarsym _) }
  CONSYM { L _ (ITconsym _) }
  QVARID { L _ (ITqvarid _)}
  QCONID { L _ (ITqconid _) }
  QVARSYM { L _ (ITqvarsym _) }
  QCONSYM { L _ (ITqconsym _) }

  CHAR { L _ (ITchar _ _) }
  STRING { L _ (ITstring _ _) }
  INTEGER { L _ (ITinteger _) }
  RATIONAL { L _ (ITrational _) }

%monad { P } { >>= } { return }
%lexer { (lexerDbg True) } { L _ ITeof }
%tokentype { (Located Token) }

%name parseModuleNoHaddock module
-- %name parseImport importdecl
-- %name parseDeclaration topdecl
-- %name parseExpression exp
-- %name parseTypeSignature sigdecl
-- %name parseType ktype
%partial parseHeader header
%%

-----------------------------------------------------------------------------
-- Module Header

module :: { Located (CsModule Ps) }
  : 'module' modid maybeexports 'where' body
      {% fileSrcSpan >>= \ loc ->
         acsFinal (\cs eof -> (L loc (CsModule
                                       (XModulePs
                                        (EpAnn (spanAsAnchor loc)
                                               (AnnsModule [ mj AnnModule $1
                                                           , mj AnnWhere $4 ]
                                                           (fstOf3 $5) [] eof)
                                               cs)
                                        (thdOf3 $5))
                                       $2 $3
                                       (fst $ sndOf3 $5)
                                       (snd $ sndOf3 $5)))) }

body :: { ( [TrailingAnn]
          , ([LImportDecl Ps], [LCsDecl Ps])
          , EpLayout ) }
  : open top close { (fst $2, snd $2, EpVirtualBraces (getOLAYOUT $1)) }

top :: { ( [TrailingAnn]
         , ([LImportDecl Ps], [LCsDecl Ps]) ) }
  : semis top1 { (reverse $1, $2) }

top1 :: { ([LImportDecl Ps], [LCsDecl Ps]) }
  : importdecls_semi topdecls_cs_semi { (reverse $1, fromOL $2) }
  | importdecls_semi topdecls_cs { (reverse $1, fromOL $2) }
  | importdecls { (reverse $1, []) }

-----------------------------------------------------------------------------
-- Module declaration & imports only

header :: { Located (CsModule Ps) }
  : 'module' modid maybeexports 'where' header_body
       {% fileSrcSpan >>= \ loc ->
          acs loc (\loc cs -> (L loc (CsModule
                                       (XModulePs
                                         (EpAnn (spanAsAnchor loc)
                                                (AnnsModule [ mj AnnModule $1
                                                            , mj AnnWhere $4 ]
                                                            [] [] Nothing)
                                                cs)
                                         EpNoLayout)
                                       $2 $3 $5 []))) }

header_body :: { [LImportDecl Ps] }
  : OPEN_LAYOUT header_top { $2 }

header_top :: { [LImportDecl Ps] }
  : semis header_top_importdecls { $2 }

header_top_importdecls :: { [LImportDecl Ps] }
  : importdecls_semi { $1 }
  | importdecls { $1 }  

-----------------------------------------------------------------------------
-- The Export List

maybeexports :: { Maybe (LocatedL [LIE Ps]) }
  : '(' exportlist ')' {% fmap Just $ amsr (sLL $1 $> (fromOL $ snd $2))
                               (AnnList Nothing (Just $ mop $1) (Just $ mcp $3) (fst $2) []) }
  | {- empty -} { Nothing }

exportlist :: { ([AddEpAnn], OrdList (LIE Ps)) }
  : exportlist1 { ([], $1) }
  | {- empty -} { ([], nilOL) }

  -- trailing comma:
  | exportlist1 ',' {% case $1 of
                         SnocOL hs t -> do
                           t' <- addTrailingCommaA t (gl $2)
                           return ([], snocOL hs t')}
  | ',' { ([mj AnnComma $1], nilOL) }

exportlist1 :: { OrdList (LIE Ps) }
  : exportlist1 ',' export_cs {% let ls = $1
                                 in if isNilOL ls
                                    then return (ls `appOL` $3)
                                    else case ls of
                                           SnocOL hs t -> do
                                             t' <- addTrailingCommaA t (gl $2)
                                             return (snocOL hs t' `appOL` $3) }
  | export_cs { $1 }
  
export_cs :: { OrdList (LIE Ps) }
export_cs : export {% return (unitOL $1) }

export :: { LIE Ps }
  : qcname_ext export_subspec {% do { let { span = comb2 $1 $> }
                                    ; impExp <- mkModuleImpExp (fst $ unLoc $2) $1 (snd $ unLoc $2)
                                    ; return $ reLoc $ sL span $ impExp } }
  | 'module' modid {% do { let { span = comb2 $1 $>
                               ; anchor = glR $1 }
                         ; locImpExp <- return (sL span (IEModuleContents [mj AnnModule $1] $2))
                         ; return $ reLoc $ locImpExp } }

-- included for forward compatibility
export_subspec :: { Located ([AddEpAnn], ImpExpSubSpec) }
  : {- empty -} { sL0 ([], ImpExpAbs) }

qcname_ext :: { LocatedA ImpExpQcSpec }
  : a_qvar { sL1a $1 (ImpExpQcName $ fmap unknownToVar $1) }
  | 'type' a_qvar { sLLa $1 $> (ImpExpQcTyVar (glAA $1) (fmap unknownToTv $2)) }

-----------------------------------------------------------------------------
-- Import Declarations

semis1 :: { Located [TrailingAnn] }
semis1 : semis1 ';' { if isZeroWidthSpan (gl $2)
                      then sL1 $1 $ unLoc $1
                      else sLL $1 $> $ AddSemiAnn (glAA $2) : (unLoc $1) }
       | ';' { case msemi $1 of
                 [] -> noLoc []
                 ms -> sL1 $1 $ ms }

semis :: { [TrailingAnn] }
semis : semis ';' { if isZeroWidthSpan (gl $2) then $1 else (AddSemiAnn (glAA $2) : $1) }
      | {- empty -} { [] }

importdecls :: { [LImportDecl Ps] }
  : importdecls_semi importdecl { $2 : $1}

importdecls_semi :: { [LImportDecl Ps] }
  : importdecls_semi importdecl semis1 {% do { i <- amsAl $2 (comb2 $2 $3) (reverse $ unLoc $3)
                                             ; return (i : $1) } }
  | {- empty -} { [] }

importdecl :: { LImportDecl Ps }
  : 'import' modid optqualified maybeas maybeimpspec
      {% do { let { mPostQual = unLoc $3
                  ; anns = EpAnnImportDecl
                           { importDeclAnnImport = glAA $1
                           , importDeclAnnQualified = mPostQual
                           , importDeclAnnPackage = Nothing
                           , importDeclAnnAs = fst $4
                           }
                  ; loc = comb5 $1 $2 $3 (snd $4) $5 }
            ; fmap reLoc $ acs loc (\ loc cs -> L loc $
                ImportDecl { ideclExt = XImportDeclPass (EpAnn (spanAsAnchor loc) anns cs)
                                                        NoSourceText False
                           , ideclName = $2
                           , ideclPkgQual = NoRawPkgQual
                           , ideclQualified = snd $ importDeclQualifiedStyle mPostQual
                           , ideclAs = unLoc (snd $4)
                           , ideclImportList = unLoc $5 }) } }

optqualified :: { Located (Maybe EpaLocation) }
  : 'qualified' { sL1 $1 (Just (glAA $1)) }
  | {- empty -} { noLoc Nothing }

maybeas :: { (Maybe EpaLocation, Located (Maybe (LocatedA ModuleName))) }
  : 'as' modid { (Just (glAA $1), sLL $1 $> (Just $2)) }
  | {- empty -} { (Nothing, noLoc Nothing) }

maybeimpspec :: { Located (Maybe (ImportListInterpretation, LocatedL [LIE Ps])) }
  : impspec {% let (b, ie) = unLoc $1
               in checkImportSpec ie
                  >>= \ checkedIe -> return (L (gl $1) (Just (b, checkedIe))) }
  | {- empty -} { noLoc Nothing }

impspec :: { Located (ImportListInterpretation, LocatedL [LIE Ps]) }
  : '(' importlist ')' {% do { es <- amsr (sLL $1 $> $ fromOL $ snd $2)
                                          (AnnList Nothing (Just $ mop $1)
                                                   (Just $ mcp $3) (fst $2) [])
                             ; return $ sLL $1 $> (Exactly, es) } }
  | 'hiding' '(' importlist ')' {% do { es <- amsr (sLL $1 $> $ fromOL $ snd $3)
                                                   (AnnList Nothing (Just $ mop $2)
                                                            (Just $ mcp $4)
                                                            (mj AnnHiding $1:fst $3) [])
                                      ; return $ sLL $1 $> (EverythingBut, es) } }

importlist :: { ([AddEpAnn], OrdList (LIE Ps)) }
  : importlist1 { ([], $1) }
  | {- empty -} { ([], nilOL) }
  | importlist1 ',' {% case $1 of
                        SnocOL hs t -> do
                          { t' <- addTrailingCommaA t (gl $2)
                          ; return ([], snocOL hs t') } }
  | ',' { ([mj AnnComma $1], nilOL) }

importlist1 :: { OrdList (LIE Ps) }
  : importlist1 ',' import {% let ls = $1
                              in if isNilOL ls
                                 then return (ls `appOL` $3)
                                 else case ls of
                                        SnocOL hs t -> do
                                          { t' <- addTrailingCommaA t (gl $2)
                                          ; return (snocOL hs t' `appOL` $3) } }
  | import { $1 }

import :: { OrdList (LIE Ps) }
  : qcname_ext export_subspec {% fmap (unitOL . reLoc . (sLL $1 $>)) $
                                mkModuleImpExp (fst $ unLoc $2) $1 (snd $ unLoc $2) }
  | 'module' modid {% fmap (unitOL . reLoc) $
                     return (sLL $1 $> (IEModuleContents [mj AnnModule $1] $2)) }

-----------------------------------------------------------------------------
-- Fixity Declarations

prec :: { Located (SourceText, Int) }
  : INTEGER { sL1 $1 (getINTEGERs $1, fromInteger (il_value (getINTEGER $1))) }

infix :: { Located FixityDirection }
  : 'infix' { sL1 $1 InfixN }
  | 'infixl' { sL1 $1 InfixL }
  | 'infixr' { sL1 $1 InfixR }

namespace_spec :: { Located NamespaceSpecifier }
  : 'type' { sL1 $1 $ TypeNamespaceSpecifier (epTok $1) }
  | {- empty -} { sL0 $ NoNamespaceSpecifier }

-----------------------------------------------------------------------------
-- Top-Level Declarations

topdecls_cs :: { OrdList (LCsDecl Ps) }
  : topdecls_cs_semi topdecl_cs { $1 `snocOL` $2 }

topdecls_cs_semi :: { OrdList (LCsDecl Ps) }
  : topdecls_cs_semi topdecl_cs semis1 {% do { t <- amsAl $2 (comb2 $2 $3) (reverse $ unLoc $3)
                                             ; return ($1 `snocOL` t) } }
  | {- empty -} { nilOL }

topdecl_cs :: { LCsDecl Ps }
  : topdecl {% commentsPA $1 }

topdecl :: { LCsDecl Ps }
  : ty_decl { L (getLoc $1) (ValD noExtField (unLoc $1)) }
  | decl { $1 }

-----------------------------------------------------------------------------
-- Type definitions

ty_decl :: { LCsBind Ps }
  : 'type' a_var '=' context_exp {% runPV (unETP $4) >>= \ $4 ->
                                    mkTyFunBind (comb2 $1 $4) (fmap unknownToTv $2) $4
                                                 [mj AnnType $1, mj AnnEqual $3] }

-----------------------------------------------------------------------------
-- Value definitions

decl :: { LCsDecl Ps }
  : sigdecl { $1 }
  | a_var '=' sig_exp {% runPV (unETP $3) >>= \ $3 ->
                      amsA' $ sLL $1 $> $ ValD noExtField $
                       FunBind (mj AnnEqual $2) (fmap unknownToVar $1) $3 }

sigdecl :: { LCsDecl Ps }
  : a_var ':' sigtype {% amsA' $ sLL $1 $> $ SigD noExtField $
                           TypeSig (AnnSig (mu AnnColon $2) []) (fmap unknownToVar $1) $3 }

  | infix prec namespace_spec a_infix_decl_op
      {% do { checkPrecP $2 $4
            ; let { precAnn = mj AnnVal $2
                  ; (fixText, fixPrec) = (fst $ unLoc $2, snd $ unLoc $2)
                  ; opWithNS = case unLoc $3 of
                                 NoNamespaceSpecifier
                                   | isConOccFS (rdrNameOcc (unLoc $4)) -> fmap unknownToData $4
                                   | otherwise -> fmap unknownToVar $4
                                 TypeNamespaceSpecifier _
                                   | isConOccFS (rdrNameOcc (unLoc $4)) -> fmap unknownToTcCls $4
                                   | otherwise -> fmap unknownToTv $4 }
            ; amsA' (sLL $1 $> $ SigD noExtField
                     (FixSig (mj AnnInfix $1 : [precAnn], fixText)
                             (FixitySig (unLoc $3) opWithNS
                                        (Fixity fixPrec (unLoc $1))))) } }

-- this can be removed:
-- split infix delc in 'sigdecl' into two rules, one for var and one for con.
-- this should reduce the logic needed to determine namespace, but has some code duplication.
-- The namespace can't be set here
a_infix_decl_op :: { LocatedN RdrName }
  : a_varop { $1 }
  | a_conop { $1 }

-----------------------------------------------------------------------------
-- Type signatures

sigtype :: { LCsSigType Ps }
  : context_exp {% fmap csTypeToCsSigType (runPV (unETP $1)) }

-----------------------------------------------------------------------------
-- Types

-- context_type :: { LCsType Ps }
--   : context '=>' exp {% runPV (unETP $3) >>= \ $3 ->
--                           acsA (comb2 $1 $>) (\loc cs -> (L loc $
--                             CsQualTy { cst_ctxt = addTrailingDarrowC $1 $2 cs
--                                      , cs_xqual = noExtField
--                                      , cst_body = $3 })) }
--   | exp {% runPV (unETP $1) }

-----------------------------------------------------------------------------
-- Type Binders

tv_bndrs :: { [LCsTyVarBndr Ps] }
  : tv_bndr { [$1] }
  | tv_bndrs1 { reverse $1 }

tv_bndr :: { LCsTyVarBndr Ps }
  : a_var ':' aexp1 {% runPV (unETP $3) >>= \ ($3 :: LCsKind Ps) ->
                      amsA' (sLL $1 $> (KindedTyVar [mu AnnColon $2] (fmap unknownToTv $1) $3)) }

tv_bndrs1 :: { [LCsTyVarBndr Ps] }
  : tv_bndrs1 tv_bndr_parens { $2 : $1 }
  -- | {- empty -} %shift { [] }
  | tv_bndr_parens { [$1] }

tv_bndr_parens :: { LCsTyVarBndr Ps }
  : '(' a_var ':' aexp1 ')' {% runPV (unETP $4) >>= \ ($4 :: LCsKind Ps) ->
                              amsA' (sLL $1 $> (KindedTyVar [mop $1, mu AnnColon $3, mcp $5]
                                                            (fmap unknownToTv $2) $4)) }
  | '{' a_var ':' aexp1 '}'
           {% runPV (unETP $4) >>= \ ($4 :: LCsKind Ps) ->
              amsA' (sLL $1 $> (ImpKindedTyVar [ mu AnnOpenC $1
                                               , mu AnnColon $3
                                               , mu AnnCloseC $5 ]
                                 (fmap unknownToTv $2) $4)) }

-----------------------------------------------------------------------------
-- Argument patterns

-- argpats :: { [LPat Ps] }
--   : argpat { [$1] }
--   | argpats1 { reverse $1 }

-- argpat :: { LPat Ps }
--   : sig_exp {% (checkPattern <=< runPV) (unETP $1) }

-- argpats1 :: { [LPat Ps] }
--   : argpats1 argpat1 { $2 : $1 }
--   | argpat1 { [$1] }
  
-- argpat1 :: { LPat Ps }
--   : aexp {% (checkPattern <=< runPV) (unETP $1) }

-- argpats :: { ETP }
--   : sig_exp { ETP $ unETP $1 >>= \ $1 ->
--               mkCsPatListPV $1 }
--   | argpats1 { $1 }

argpats :: { ETP }
  : argpats aexp { ETP $ unETP $1 >>= \ $1 ->
                         unETP $2 >>= \ $2 ->
                         mkCsPatListConsPV $1 $2 }
  | aexp { ETP $ unETP $1 >>= \ $1 ->
           mkCsPatListPV $1 }
  
-----------------------------------------------------------------------------
-- Type argument patterns

-- tyargpats :: { [LPat Ps] }
--   : tyargpat { [$1 ] }
--   | tyargpats1 { L (getLoc $1) (reverse (unLoc $1)) }

-- tyargpat :: { LPat Ps }
--   : sig_exp {% (checkTyPattern <=< runPV) (unETP $1) }

-- tyargpats1 :: { [LPat Ps] }
--   : tyargpats1 tyargpat1 { $2 : $1 }
--   | tyargpat1 { [$1] }

-- tyargpat1 :: { LPat Ps }
--   : aexp1 {% (checkTyPattern <=< runPV) (unETP $1) }

-----------------------------------------------------------------------------
-- Kinds

-- We should have this rule, but it introduces reduce/reduce ambiguity with 'aexp -> aexp1'
-- kind :: { LCsKind Ps }
--   : aexp1 {% runPV (unETP $1) }

-----------------------------------------------------------------------------
-- Type and Value Expressions 

context_exp :: { ETP }
  : quant_exp { $1 }
  | context '=>' quant_exp {% runPV (unETP $3) >>= \ ($3 :: LCsType Ps) -> do
                               { qualTy <- acsA (comb2 $1 $>) (\loc cs ->
                                                                 L loc $
                                                                 CsQualTy
                                                                 { cst_ctxt =
                                                                     addTrailingDarrowC $1 $2 cs
                                                                 , cst_xqual = noExtField
                                                                 , cst_body = $3 })
                               ; return $ etpFromTy qualTy } }

context :: { LCsContext Ps }
  : context1 { L (getLoc $1) (reverse (unLoc $1)) }

context1 :: { LCsContext Ps }
  : '(' context ')' { case $2 of
                        L (EpAnn l (AnnContext m oparens cparens) cs) ctxt ->
                          L (EpAnn l (AnnContext m (glAA $1 : oparens) (glAA $3 : cparens)) cs)
                            ctxt }
  | context1 ',' kvrel {% case unLoc $1 of
                            (h:t) -> do { h' <- addTrailingCommaA h (gl $2)
                                        ; return (sLLc $1 $> ($3 : (h':t))) } }
  | kvrel { sL1a $1 [$1] }

kvrel :: { LCsKdRel Ps }
  : aexp1 a_varsym aexp1 {% runPV (unETP $1) >>= \ ($1 :: LCsKind Ps) ->
                            runPV (unETP $3) >>= \ ($3 :: LCsKind Ps) ->
                                  mkKvRel (comb2 $1 $3) $1 $2 $3 }


quant_exp :: { ETP }
  : forall_telescope quant_exp {% runPV (unETP $2) >>= \ ($2 :: LCsType Ps) ->
                                  let forallTy = sLLa $1 $> $ CsForAllTy
                                                              { cst_tele = unLoc $1
                                                              , cst_xforall = noExtField
                                                              , cst_body = $2 }
                                  in return $ etpFromTy forallTy }
  | fun_exp %shift { $1 }

forall_telescope :: { Located (CsForAllTelescope Ps) }
  : 'forall' tv_bndrs '.' {% acs (comb2 $1 $>) (\loc cs -> (L loc $
                                    mkCsForAllTele (EpAnn (glEE $1 $>)
                                                          ( mu AnnForall $1
                                                          , mu AnnDot $3) cs) $2)) }

fun_exp :: { ETP }
  : sig_exp %shift { $1 }
  | sig_exp ARR_U quant_exp {% runPV $ unETP $1 >>= \ ($1 :: LCsType Ps) ->
                                       unETP $3 >>= \ ($3 :: LCsType Ps) -> do
                                       { res <- amsA' (sLL $1 $>
                                                       $ CsFunTy noExtField
                                                         (CsArrow (EpU $ epUniTok $2)
                                                                  (sL1a $2 $ CsUKd noExtField))
                                                         $1 $3)
                                       ; return $ etpFromTy res } }
  | sig_exp ARR_A quant_exp {% runPV $ unETP $1 >>= \ ($1 :: LCsType Ps) ->
                                       unETP $3 >>= \ ($3 :: LCsType Ps) -> do
                                       { res <- amsA' (sLL $1 $>
                                                     $ CsFunTy noExtField
                                                       (CsArrow (EpA $ epUniTok $2)
                                                                (sL1a $2 $ CsAKd noExtField))
                                                       $1 $3)
                                       ; return $ etpFromTy res } }
  | sig_exp ARR_L quant_exp {% runPV $ unETP $1 >>= \ ($1 :: LCsType Ps) ->
                                       unETP $3 >>= \ ($3 :: LCsType Ps) -> do
                                       { res <- amsA' (sLL $1 $>
                                                     $ CsFunTy noExtField
                                                       (CsArrow (EpL $ epUniTok $2)
                                                                (sL1a $2 $ CsLKd noExtField))
                                                       $1 $3)
                                       ; return $ etpFromTy res } }
  | sig_exp ARR_K quant_exp {% runPV $ unETP $1 >>= \ ($1 :: LCsType Ps) ->
                                       unETP $3 >>= \ ($3 :: LCsType Ps) -> do
                                       { let loc = shrinkSrcSpan $ getHasLoc $2
                                       ; res <- amsA' (sLL $1 $>
                                                     $ CsFunTy noExtField
                                                       (CsArrow (EpL $ epUniTok $2)
                                                                (L (noAnnSrcSpan loc)
                                                                 $ CsKdVar []
                                                                     (L (noAnnSrcSpan loc)
                                                                      $ mkUnqual kvName
                                                                      $ getARRK $2)))
                                                       $1 $3)
                                       ; return $ etpFromTy res } }
  -- | sig_exp PREFIX_MINUS aexp SUFFIX_ARR quant_exp
  --   {% runPV $ unETP $1 >>= \ ($1 :: LCsType Ps) ->
  --              unETP $3 >>= \ ($3 :: LCsKind Ps) ->
  --              unETP $5 >>= \ ($5 :: LCsType Ps) -> do
  --              { kind <- amsA' $ sLL $2 $4 (unLoc $3) -- $ CsKdVar [] (fmap unknownToKv $3)
  --              ; res <- amsA' (sLL $1 $>
  --                            $ CsFunTy noExtField
  --                              -- (CsArrow (EpVar $ fmap unknownToKv $3) kind)
  --                              (CsArrow (EpVar $ sL1n (comb2 $2 $4)
  --                                              $ mkUnqual kvName (fsLit "kT")) kind)
  --                              $1 $5)
  --              ; return $ etpFromTy res } }
  | fun_exp '->' aexp1 {% runPV $ unETP $1 >>= \ ($1 :: LCsKind Ps) ->
                                  unETP $3 >>= \ ($3 :: LCsKind Ps) -> do
                                  { res <- amsA' (sLL $1 $3 $ CsFunKd noExtField $1 $3)
                                  ; return $ etpFromKd res } }

sig_exp :: { ETP }
  : infixexp ':' context_exp { ETP $ superSigPV $
                                     unETP $1 >>= \ $1 ->
                                     unETP $3 >>= \ $3 ->
                                     mkCsSigPV (noAnnSrcSpan $ comb2 $1 $>) $1 $3
                                               [(mu AnnColon $2)] }
  | infixexp %shift { $1 }

infixexp :: { ETP }
  : app_exp10 %shift { $1 }
  | infixexp a_qvarop app_exp10 { ETP $ unETP $1 >>= \ $1 ->
                                        unETP $3 >>= \ $3 ->
                                        mkCsOpAppPV (comb2 $1 $3) $1 $2 $3 }
  | infixexp a_qconop app_exp10 { ETP $ unETP $1 >>= \ $1 ->
                                        unETP $3 >>= \ $3 ->
                                        mkCsConOpAppPV (comb2 $1 $3) $1 $2 $3 }

app_exp10 :: { ETP }
  : app_exp %shift { $1 }
  
app_exp :: { ETP }
  : app_exp aexp { ETP $ unETP $1 >>= \ $1 ->
                         unETP $2 >>= \ $2 ->
                         spanWithComments (comb2 $1 $>) >>= \ l ->
                         mkCsAppPV l $1 $2 }
  | aexp %shift { $1 }

aexp :: { ETP }
  : a_qvar TIGHT_INFIX_AT aexp { ETP $ unETP $3 >>= \ $3 ->
                                       mkCsAsPatPV (comb2 $1 $>) $1 (epTok $2) $3 }
  | PREFIX_MINUS aexp { ETP $ unETP $2 >>= \ $2 ->
                              mkCsNegAppPV (comb2 $1 $>) $2 [mj AnnMinus $1] }
  | 'let' bind 'in' sig_exp { ETP $ unETP $4 >>= \ $4 ->
                                mkCsLetPV (comb2 $1 $>) (epTok $1) (unLoc $2) (epTok $3) $4 }
  | '\\' argpats '->' sig_exp { ETP $ superArgBuilderPV $
                                      unETP $2 >>= \ $2 ->
                                      unETP $4 >>= \ $4 ->
                                  mkCsLamPV (comb2 $1 $>) $2
                                    (\ctxt (L _ pats) -> sLLl $1 $>
                                     [sLLa $1 $> $ Match
                                      { m_ext = []
                                      , m_ctxt = ctxt
                                      , m_pats = L (listLocation pats) pats
                                      , m_grhss = unguardedGRHSs
                                                  (comb2 $3 $4) $4
                                                  (EpAnn (glR $3)
                                                         (GrhsAnn Nothing (mu AnnRarrow $3))
                                                         emptyComments) }])
                                    [mj AnnLam $1] }
  | '/\\' argpats '->' sig_exp { ETP $ unETP $2 >>= \ $2 ->
                                       unETP $4 >>= \ $4 -> do
                                       { L _ pats <- checkLTyArgListPat $2
                                       ; mkCsTyLamPV (comb2 $1 $>)
                                         (sLLl $1 $>
                                          [sLLa $1 $> $ Match
                                           { m_ext = []
                                           , m_ctxt = TyLamAlt
                                           , m_pats = L (listLocation pats) pats
                                           , m_grhss = unguardedGRHSs
                                                       (comb2 $3 $4) $4
                                                       (EpAnn (glR $3)
                                                              (GrhsAnn Nothing (mu AnnRarrow $3))
                                                              emptyComments) }])
                                         [mj AnnTyLam $1] } }
  | 'if' sig_exp optSemi 'then' sig_exp optSemi 'else' sig_exp
    {% runPV (unETP $2) >>= \ ($2 :: LCsExpr Ps) ->
         return $ ETP $
           unETP $5 >>= \ $5 ->
           unETP $8 >>= \ $8 ->
           mkCsIfPV (comb2 $1 $>) $2 (snd $3) $5 (snd $6) $8
                    (AnnsIf
                     { aiIf = glAA $1
                     , aiThen = glAA $4
                     , aiElse = glAA $7
                     , aiThenSemi = fst $3
                     , aiElseSemi = fst $6 }) }
  | 'if' ifgdpats {% fmap etpFromExp $
                     amsA' (sLL $1 $> $ CsMultiIf (mj AnnIf $1 : (fst $ unLoc $2))
                                                  (reverse $ snd $ unLoc $2)) }
  | 'case' sig_exp 'of' altslist(pats1) {% runPV (unETP $2) >>= \ ($2 :: LCsExpr Ps) ->
                                       return $ ETP $
                                       $4 >>= \ $4 ->
                                       mkCsCasePV (comb3 $1 $3 $4) $2 $4
                                                  (EpAnnCsCase (glAA $1) (glAA $3) []) }
  | aexp1 %shift { $1 }

aexp1 :: { ETP }
  : a_qvar { ETP $ mkCsVarPV $! $1 }
  | a_qcon { ETP $ mkCsConPV $! $1 }
  | literal { ETP $ mkCsLitPV $! $1 }
  | STRING { ETP $ mkCsOverLitPV (sL1a $1 $ mkCsIsString (getSTRINGs $1) (getSTRING $1)) }
  | INTEGER { ETP $ mkCsOverLitPV (sL1a $1 $ mkCsIntegral (getINTEGER $1)) }
  | RATIONAL { ETP $ mkCsOverLitPV (sL1a $1 $ mkCsFractional (getRATIONAL $1)) }
  | '(' texp ')' { ETP $ unETP $2 >>= \ $2 ->
                         mkCsParPV (comb2 $1 $>) (epTok $1) $2 (epTok $3) }
  | '(' tup_exprs ')' { ETP $ $2 >>= \ $2 ->
                              mkCsSumOrTuplePV (noAnnSrcSpan $ comb2 $1 $>) $2 [mop $1, mcp $3] }
  | '_' { ETP $ mkCsWildCardPV (getLoc $1) }
  | '{' context_exp '}' { ETP $ superBracesPV $
                                unETP $2 >>= \ $2 ->
                                mkCsInBracesPV (comb2 $1 $>) $2 [moc $1, mcc $3] }
  -- these should be part of a_qcon from syscon, but they cannot have type RdrName, since
  -- they would lose the kind information
  | '(' ARR_U ')' {% do { kind <- amsA' $ sL1 $2 $ CsUKd noExtField
                        ; name <- amsA' $ sL1 $2 $ getRdrName unrestrictedFUNTyCon
                        ; tyvar <- amsA' $ sL1 $2 $ CsTyVar [] name
                        ; funty <- amsA' $ sL1 $2 $ CsKindSig [] tyvar kind
                        ; res <- amsA' $ sLL $1 $>
                                 $ CsParTy (epTok $1, epTok $3) funty
                        ; return $ etpFromTy res } }
  | '(' ARR_A ')' {% do { kind <- amsA' $ sL1 $2 $ CsAKd noExtField
                        ; name <- amsA' $ sL1 $2 $ getRdrName unrestrictedFUNTyCon
                        ; tyvar <- amsA' $ sL1 $2 $ CsTyVar [] name
                        ; funty <- amsA' $ sL1 $2 $ CsKindSig [] tyvar kind
                        ; res <- amsA' $ sLL $1 $>
                                 $ CsParTy (epTok $1, epTok $3) funty
                        ; return $ etpFromTy res } }
  | '(' ARR_L ')' {% do { kind <- amsA' $ sL1 $2 $ CsLKd noExtField
                        ; name <- amsA' $ sL1 $2 $ getRdrName unrestrictedFUNTyCon
                        ; tyvar <- amsA' $ sL1 $2 $ CsTyVar [] name
                        ; funty <- amsA' $ sL1 $2 $ CsKindSig [] tyvar kind
                        ; res <- amsA' $ sLL $1 $>
                                 $ CsParTy (epTok $1, epTok $3) funty
                        ; return $ etpFromTy res } }
  | '(' PREFIX_MINUS a_varid SUFFIX_ARR ')'
                  {% do { kind <- amsA' $ sL1 $3 $ CsKdVar [] (fmap unknownToKv $3)
                        ; name <- amsA' $ sLL $2 $4 $ getRdrName fUNTyCon
                        ; tyvar <- amsA' $ sLL $2 $4 $ CsTyVar [] name
                        ; funty <- amsA' $ sLL $2 $4 $ CsKindSig [] tyvar kind
                        ; res <- amsA' $ sLL $1 $>
                                 $ CsParTy (epTok $1, epTok $5) funty
                        ; return $ etpFromTy res } }
  | U_KIND { etpFromKd $ sL1a $1 (CsUKd noExtField) }
  | A_KIND { etpFromKd $ sL1a $1 (CsAKd noExtField) }
  | L_KIND { etpFromKd $ sL1a $1 (CsLKd noExtField) }

-----------------------------------------------------------------------------
-- Tuple expressions

texp :: { ETP }
  : quant_exp { $1 }
  | infixexp a_qvarop { ETP $ unETP $1 >>= \ $1 ->
                              mkCsVarSectionL (comb2 $1 $2) $1 $2 }
  | infixexp a_qconop { ETP $ unETP $1 >>= \ $1 ->
                              mkCsConSectionL (comb2 $1 $2) $1 $2 }
  | a_qvarop infixexp { ETP $ unETP $2 >>= \ $2 ->
                              mkCsVarSectionR (comb2 $1 $2) $1 $2 }
  | a_qconop infixexp { ETP $ unETP $2 >>= \ $2 ->
                              mkCsConSectionR (comb2 $1 $2) $1 $2 }
  
tup_exprs :: { forall b. DisambETP b => PV (SumOrTuple b) }
  : texp commas_tup_tail { unETP $1 >>= \ $1 ->
                           $2 >>= \ $2 -> do
                           { t <- amsA $1 [AddCommaAnn (srcSpan2e $ fst $2)]
                           ; return (Tuple (Right t : snd $2)) } }
  | commas tup_tail { $2 >>= \ $2 ->
                      let cos = map (\ ll -> Left (EpAnn (spanAsAnchor ll) True emptyComments))
                                    (fst $1)
                      in return (Tuple (cos ++ $2)) }
  | texp bars { unETP $1 >>= \ $1 -> return $ Sum 1 (snd $2 + 1) $1 [] (map srcSpan2e $ fst $2) }
  | bars texp bars0 { unETP $2 >>= \ $2 -> return $
                      Sum (snd $1 + 1) (snd $1 + snd $3 + 1) $2 (map srcSpan2e $ fst $1)
                                                                (map srcSpan2e $ fst $3) }

commas_tup_tail :: { forall b. DisambETP b => PV (SrcSpan, [Either (EpAnn Bool) (LocatedA b)]) }
  : commas tup_tail { $2 >>= \ $2 ->
                      let cos = map (\l -> Left (EpAnn (spanAsAnchor l) True emptyComments))
                                    (tail $ fst $1)
                      in return ((head $ fst $1, cos ++ $2)) }

tup_tail :: { forall b. DisambETP b => PV [Either (EpAnn Bool) (LocatedA b)] }
  : texp commas_tup_tail { unETP $1 >>= \ $1 ->
                           $2 >>= \ $2 -> do
                           { t <- amsA $1 [AddCommaAnn (srcSpan2e $ fst $2)]
                           ; return (Right t : snd $2) } }
  | texp { unETP $1 >>= \ $1 -> return [Right $1] }
  | {- empty -} %shift { return [Left noAnn] }

-----------------------------------------------------------------------------
-- Multiway if

ifgdpats :: { Located ([AddEpAnn], [LGRHS Ps (LCsExpr Ps)]) }
  : gdpats close {% runPV $1 >>= \ $1 -> return $ sL1 $1 ([], unLoc $1) }

-----------------------------------------------------------------------------
-- Statements

qual :: { forall b. DisambETP b => PV (LStmt Ps (LocatedA b)) }
  : bindpat '<-' sig_exp { unETP $3 >>= \ $3 ->
                       amsA' (sLL $1 $> $ mkPsBindStmt [mu AnnLarrow $2] $1 $3) }
  | sig_exp { unETP $1 >>= \ $1 -> return $ sL1a $1 $ mkBodyStmt $1 }
  | 'let' bind { amsA' (sLL $1 $> $ mkLetStmt [mj AnnLet $1] (unLoc $2)) }

-----------------------------------------------------------------------------
-- Guards

guardquals :: { Located [LStmt Ps (LCsExpr Ps)] }
  : guardquals1 { L (getLoc $1) (reverse (unLoc $1)) }

guardquals1 :: { Located [LStmt Ps (LCsExpr Ps)] }
  : guardquals1 ',' qual {% runPV $3 >>= \ $3 ->
                            case unLoc $1 of
                              (h:t) -> do
                                { h' <- addTrailingCommaA h (gl $2)
                                ; return (sLL $1 $> ($3 : (h':t))) } }
  | qual {% runPV $1 >>= \ $1 -> return $ sL1 $1 [$1] }

-----------------------------------------------------------------------------
-- Case alternatives

pats1 :: { [LPat Ps] }
  : bindpat { [$1] }

altslist(PATS) :: { forall b. DisambETP b => PV (LocatedL [LMatch Ps (LocatedA b)]) }
  : open alts(PATS) close { $2 >>= \ $2 -> amsr
                             (L (getLoc $2) (reverse (snd $ unLoc $2)))
                             (AnnList (Just $ glR $2) Nothing Nothing (fst $ unLoc $2) []) }
  | open close { return $ noLocA [] }

alts(PATS) :: { forall b. DisambETP b => PV (Located ([AddEpAnn], [LMatch Ps (LocatedA b)])) }
  : alts1(PATS) { $1 >>= \ $1 -> return $
                  sL1 $1 (fst $ unLoc $1, snd $ unLoc $1) }
  | ';' alts(PATS) { $2 >>= \ $2 -> return $
                     sLL $1 $> ( ((mz AnnSemi $1) ++ (fst $ unLoc $2) )
                               , snd $ unLoc $2) }

alts1(PATS) :: { forall b. DisambETP b => PV (Located ([AddEpAnn], [LMatch Ps (LocatedA b)])) }
  : alts1(PATS) ';' alt(PATS) { $1 >>= \ $1 ->
                                $3 >>= \ $3 ->
                                  case snd $ unLoc $1 of
                                    [] -> return (sLL $1 $> ( (fst $ unLoc $1) ++ (mz AnnSemi $2)
                                                            , [$3] ))
                                    (h:t) -> do
                                      { h' <- addTrailingSemiA h (gl $2)
                                      ; return (sLZ $1 $> (fst $ unLoc $1, h':t)) } }
  | alt(PATS) { $1 >>= \ $1 -> return $ sL1 $1 ([], [$1]) }

alt(PATS) :: { forall b. DisambETP b => PV (LMatch Ps (LocatedA b)) }
  : PATS alt_rhs { $2 >>= \ $2 ->
                   amsA' (sLLAsl $1 $>
                          (Match { m_ext = []
                                 , m_ctxt = CaseAlt
                                 , m_pats = L (listLocation $1) $1
                                 , m_grhss = unLoc $2 })) }

alt_rhs :: { forall b. DisambETP b => PV (Located (GRHSs Ps (LocatedA b))) }
  : ralt { $1 >>= \ alt -> let L l a = alt in acs l (\ loc cs -> L loc (GRHSs cs a)) }

ralt :: { forall b. DisambETP b => PV (Located [LGRHS Ps (LocatedA b)]) }
  : '->' sig_exp { unETP $2 >>= \ $2 ->
               acs (comb2 $1 $>) (\ loc cs -> L loc (unguardedRHS
                                                     (EpAnn (spanAsAnchor $ comb2 $1 $2)
                                                            (GrhsAnn Nothing (mu AnnRarrow $1))
                                                            cs)
                                                      (comb2 $1 $2) $2)) }
  | gdpats { $1 >>= \ gdpats -> return $ sL1 gdpats (reverse (unLoc gdpats)) }

gdpats :: { forall b . DisambETP b => PV (Located [LGRHS Ps (LocatedA b)]) }
  : gdpats gdpat { $1 >>= \ gdpats ->
                   $2 >>= \ gdpat ->
                   return $ sLL gdpats gdpat ( gdpat : unLoc gdpats) }
  | gdpat { $1 >>= \ gdpat -> return $ sL1 gdpat [gdpat] }

gdpat :: { forall b. DisambETP b => PV (LGRHS Ps (LocatedA b)) }
  : '|' guardquals '->' sig_exp { unETP $4 >>= \ $4 ->
                              acsA (comb2 $1 $>)
                                   (\ loc cs -> sL loc $
                                        GRHS (EpAnn (glEE $1 $>)
                                                    (GrhsAnn (Just $ glAA $1) (mu AnnRarrow $3))
                                                    cs)
                                             (unLoc $2) $4) }

-----------------------------------------------------------------------------
-- Let bind

decllistone :: { Located (AnnList, Located (OrdList (LCsDecl Ps))) }
  : open decl close { let d = sL1 $2 ([], unitOL $2)  
                     in L (gl d) ( AnnList (Just $ glR d) Nothing Nothing (fst $ unLoc d) []
                                  , sL1 d $ snd $ unLoc d ) }

bind :: { Located (CsLocalBinds Ps) }
  : decllistone {% do { val_bind <- cvBindGroup (unLoc $ snd $ unLoc $1)
                      ; !cs <- getCommentsFor (gl $1)
                      ; return (sL1 $1 $ CsValBinds (fixValbindsAnn $ EpAnn
                                 (glR $1) (fst $ unLoc $1) cs) val_bind) } }

bindpat :: { LPat Ps }
  : sig_exp {% (checkPattern <=< runPV) (unETP $1) }

-----------------------------------------------------------------------------
-- Ambiguous names

-- Variables

a_var :: { LocatedN RdrName }
  : a_varid { $1 }
  | '(' a_varsym ')' {% amsr (sLL $1 $> (unLoc $2))
                             (NameAnn NameParens (glAA $1) (glAA $2) (glAA $3) []) }

a_qvar :: { LocatedN RdrName }
  : a_qvarid { $1 }
  | '(' a_qvarsym ')' {% amsr (sLL $1 $> (unLoc $2))
                             (NameAnn NameParens (glAA $1) (glAA $2) (glAA $3) []) }

-- Variable Ops

a_varop :: { LocatedN RdrName }
  : a_varsym { $1}
  | '`' a_varid '`' {% amsr (sLL $1 $> (unLoc $2))
                            (NameAnn NameBackquotes (glAA $1) (glAA $2) (glAA $3) []) }

a_qvarop :: { LocatedN RdrName }
  : a_qvarsym { $1 }
  | '`' a_qvarid '`' {% amsr (sLL $1 $> (unLoc $2))
                             (NameAnn NameBackquotes (glAA $1) (glAA $2) (glAA $3) []) }

-- Ids

a_varid :: { LocatedN RdrName }
  : VARID { sL1n $1 $! mkUnqual UNKNOWN_NS (getVARID $1) }

a_qvarid :: { LocatedN RdrName }
  : a_varid %shift { $1 }
  | QVARID { sL1n $1 $! mkQual UNKNOWN_NS (getQVARID $1) }

-- Symbols

a_varsym :: { LocatedN RdrName }
  : VARSYM { sL1n $1 $! mkUnqual UNKNOWN_NS (getVARSYM $1) }
  | '.' { sL1n $1 $ mkUnqual UNKNOWN_NS (fsLit ".") }

a_qvarsym :: { LocatedN RdrName }
  : a_varsym %shift { $1 }
  | QVARSYM { sL1n $1 $! mkQual UNKNOWN_NS (getQVARSYM $1) }

-- Constructors

a_con :: { LocatedN RdrName }
  : a_conid { $1 }
  | '(' a_consym ')' {% amsr (sLL $1 $> (unLoc $2))
                             (NameAnn NameParens (glAA $1) (glAA $2) (glAA $3) []) }
  | syscon { $1 }

a_qcon :: { LocatedN RdrName }
  : a_qconid { $1 }
  | '(' a_qconsym ')' {% amsr (sLL $1 $> (unLoc $2))
                              (NameAnn NameParens (glAA $1) (glAA $2) (glAA $3) []) }
  | syscon { $1 }

-- Con Ops

a_conop :: { LocatedN RdrName }
  : a_consym { $1 }
  | '`' a_conid '`' {% amsr (sLL $1 $> (unLoc $2))
                            (NameAnn NameBackquotes (glAA $1) (glAA $2) (glAA $3) []) }

a_qconop :: { LocatedN RdrName }
  : a_qconsym %shift { $1 }
  | '`' a_qconid '`' {% amsr (sLL $1 $> (unLoc $2))
                            (NameAnn NameBackquotes (glAA $1) (glAA $2) (glAA $3) []) }

-- Con Ids

a_conid :: { LocatedN RdrName }
  : CONID { sL1n $1 $! mkUnqual UNKNOWN_NS (getCONID $1) }

a_qconid :: { LocatedN RdrName }
  : a_conid %shift { $1 }
  | QCONID { sL1n $1 $! mkQual UNKNOWN_NS (getQCONID $1) }

-- Con Symbols

a_consym :: { LocatedN RdrName }
  : CONSYM { sL1n $1 $! mkUnqual UNKNOWN_NS (getCONSYM $1) }

a_qconsym :: { LocatedN RdrName }
  : a_consym %shift { $1 }
  | QCONSYM { sL1n $1 $! mkQual UNKNOWN_NS (getQCONSYM $1) }

-- wired-in syntax

syscon :: { LocatedN RdrName }
  : sysdcon { L (getLoc $1) $ nameRdrName (dataConName (unLoc $1)) }

sysdcon :: { LocatedN DataCon }
  : '(' commas ')' {% amsr (sLL $1 $> $ tupleDataCon (snd $2 + 1))
                           (NameAnnCommas NameParens (glAA $1)
                              (map srcSpan2e (fst $2)) (glAA $3) []) }
  | '(' ')' {% amsr (sLL $1 $> unitDataCon) (NameAnnOnly NameParens (glAA $1) (glAA $2) []) }

-----------------------------------------------------------------------------
-- Literals

literal :: { Located (CsLit Ps) }
  : CHAR { sL1 $1 $ CsChar (getCHARs $1) $ getCHAR $1 }
--  | STRING { sL1 $1 $ CsString (getSTRINGs $1) }

-----------------------------------------------------------------------------
-- Layout

open :: { Located Token }
  : OPEN_LAYOUT { $1 }

close :: { () }
  : CLOSE_LAYOUT { () }
  | error {% popContext }

optSemi :: { (Maybe EpaLocation, Bool) }
  : ';' { (msemim $1, True) }
  | {- empty -} { (Nothing, False) }

-----------------------------------------------------------------------------
-- Miscellaneous (mostly renamings)

modid :: { LocatedA ModuleName }
  : CONID { sL1a $1 $ mkModuleNameFS (getCONID $1) }
  | QCONID { sL1a $1 $ let (mod, c) = getQCONID $1
                       in mkModuleNameFS (concatFS [mod, fsLit ".", c]) }

commas :: { ([SrcSpan], Int) }
  : commas ',' { ((fst $1) ++ [gl $2], snd $1 + 1) }
  | ',' { ([gl $1], 1) }

bars0 :: { ([SrcSpan], Int) }
  : bars { $1 }
  | {- empty -} { ([], 0) }

bars :: { ([SrcSpan], Int) }
  : bars '|' { ((fst $1) ++ [gl $2], snd $1 + 1) }
  | '|' { ([gl $1], 1) }

{
happyError :: P a
happyError = srcParseFail

getVARID (L _ (ITvarid x)) = x
getCONID (L _ (ITconid x)) = x
getVARSYM (L _ (ITvarsym x)) = x
getCONSYM (L _ (ITconsym x)) = x
getQVARID (L _ (ITqvarid x)) = x
getQCONID (L _ (ITqconid x)) = x
getQVARSYM (L _ (ITqvarsym x)) = x
getQCONSYM (L _ (ITqconsym x)) = x
getCHAR (L _ (ITchar _ x)) = x
getSTRING (L _ (ITstring _ x)) = x
getINTEGER (L _ (ITinteger x)) = x
getRATIONAL (L _ (ITrational x)) = x
getOLAYOUT (L (RealSrcSpan l _) ITolayout) = srcSpanStartCol l

getARRK (L _ (ITarrowK x)) = x

getINTEGERs (L _ (ITinteger (IL src _ _))) = src
getCHARs (L _ (ITchar src _)) = src
getSTRINGs (L _(ITstring src _)) = src

isUnicode :: Located Token -> Bool
isUnicode (L _ (ITforall)) = True
isUnicode (L _ (ITstar)) = True
isUnicode (L _ (ITbullet)) = True
isUnicode (L _ (ITcirc)) = True
isUnicode (L _ (ITarrowU)) = True
isUnicode (L _ (ITarrowA)) = True
isUnicode (L _ (ITarrowL)) = True
isUnicode _ = False

-- Utilities for combining source spans
comb2 :: (HasLoc a, HasLoc b) => a -> b -> SrcSpan
comb2 !a !b = combineHasLocs a b

comb3 :: (HasLoc a, HasLoc b, HasLoc c) => a -> b -> c -> SrcSpan
comb3 !a !b !c = combineSrcSpans (getHasLoc a) (combineHasLocs b c)

comb4 :: (HasLoc a, HasLoc b, HasLoc c, HasLoc d) => a -> b -> c -> d -> SrcSpan
comb4 !a !b !c !d =
  combineSrcSpans (getHasLoc a) $
  combineSrcSpans (getHasLoc b) $
  combineSrcSpans (getHasLoc c) (getHasLoc d)

comb5 :: (HasLoc a, HasLoc b, HasLoc c, HasLoc d, HasLoc e) => a -> b -> c -> d -> e -> SrcSpan
comb5 !a !b !c !d !e =
  combineSrcSpans (getHasLoc a) $
  combineSrcSpans (getHasLoc b) $
  combineSrcSpans (getHasLoc c) $
  combineSrcSpans (getHasLoc d) (getHasLoc e)

-- strict L
{-# INLINE sL #-}
sL :: l -> a -> GenLocated l a
sL !loc !a = L loc a

-- (strict?) L with no srcSpan
{-# INLINE sL0 #-}
sL0 :: a -> Located a
sL0 = L noSrcSpan

-- strict L from HasLoc
{-# INLINE sL1 #-}
sL1 :: HasLoc a => a -> b -> Located b
sL1 !x = sL (getHasLoc x)

-- strict L from HasLoc with empty annotation
{-# INLINE sL1a #-}
sL1a :: (HasLoc a, HasAnnotation t) => a -> b -> GenLocated t b
sL1a !x = sL (noAnnSrcSpan $ getHasLoc x)

{-# INLINE sL1n #-}
sL1n :: HasLoc a => a -> b -> LocatedN b
sL1n !x = L (noAnnSrcSpan $ getHasLoc x)

{-# INLINE sLL #-}
sLL :: (HasLoc a, HasLoc b) => a -> b -> c -> Located c
sLL !x !y = sL (comb2 x y)

{-# INLINE sLLa #-}
sLLa :: (HasLoc a, HasLoc b, NoAnn t) => a -> b -> c -> LocatedAn t c
sLLa !x !y = sL (noAnnSrcSpan $ comb2 x y)

{-# INLINE sLLl #-}
sLLl :: (HasLoc a, HasLoc b) => a -> b -> c -> LocatedL c
sLLl !x !y = sL (noAnnSrcSpan $ comb2 x y)

{-# INLINE sLLc #-}
sLLc :: (HasLoc a, HasLoc b) => a -> b -> c -> LocatedC c
sLLc !x !y = sL (noAnnSrcSpan $ comb2 x y)

{-# INLINE sLLAsl #-}
sLLAsl :: (HasLoc a) => [a] -> Located b -> c -> Located c
sLLAsl [] = sL1
sLLAsl (!x:_) = sLL x

{-# INLINE sLZ #-}
sLZ :: (HasLoc a, HasLoc b) => a -> b -> c -> Located c
sLZ !x !y = if isZeroWidthSpan (getHasLoc y)
              then sL (getHasLoc x)
              else sL (comb2 x y)

fileSrcSpan :: P SrcSpan
fileSrcSpan = do
  l <- getRealSrcLoc
  let loc = mkSrcLoc (srcLocFile l) 1 1
  return (mkSrcSpan loc loc)

-- annotation helpers

mj :: AnnKeywordId -> Located e -> AddEpAnn
mj !a !l = AddEpAnn a (srcSpan2e $ gl l)

mjN :: AnnKeywordId -> LocatedN e -> AddEpAnn
mjN !a !l = AddEpAnn a (srcSpan2e $ glA l)

mz ::AnnKeywordId -> Located e -> [AddEpAnn]
mz !a !l = if isZeroWidthSpan (gl l) then [] else [AddEpAnn a (srcSpan2e $ gl l)]

msemi :: Located e -> [TrailingAnn]
msemi !l = if isZeroWidthSpan (gl l) then [] else [AddSemiAnn (srcSpan2e $ gl l)]

msemiA :: Located e -> [AddEpAnn]
msemiA !l = if isZeroWidthSpan (gl l) then [] else [AddEpAnn AnnSemi (srcSpan2e $ gl l)]

msemim :: Located e -> Maybe EpaLocation
msemim !l = if isZeroWidthSpan (gl l) then Nothing else Just (srcSpan2e $ gl l)

mu :: AnnKeywordId -> Located Token -> AddEpAnn
mu !a lt@(L l t) = AddEpAnn (toUnicodeAnn a lt) (srcSpan2e l)

toUnicodeAnn :: AnnKeywordId -> Located Token -> AnnKeywordId
toUnicodeAnn !a !t = if isUnicode t then unicodeAnn a else a

toUnicode :: Located Token -> IsUnicodeSyntax
toUnicode t = if isUnicode t then UnicodeSyntax else NormalSyntax

-- ------------------------------------

gl :: GenLocated l a -> l
gl = getLoc

glA :: HasLoc a => a -> SrcSpan
glA = getHasLoc

glR :: HasLoc a => a -> Anchor
glR !la = EpaSpan (getHasLoc la)

glEE :: (HasLoc a, HasLoc b) => a -> b -> Anchor
glEE !x !y = spanAsAnchor $ comb2 x y

glRM :: Located a -> Maybe Anchor
glRM (L !l _) = Just $ spanAsAnchor l

glAA :: HasLoc a => a -> EpaLocation
glAA = srcSpan2e . getHasLoc

n2l :: LocatedN a -> LocatedA a
n2l (L !la !a) = L (l2l la) a

acsFinal :: (EpAnnComments -> Maybe (RealSrcSpan, RealSrcSpan) -> Located a) -> P (Located a)
acsFinal a = do
  let (L l _) = a emptyComments Nothing
  !cs <- getCommentsFor l
  csf <- getFinalCommentsFor l
  meof <- getEofPos
  let ce = case meof of
             Strict.Nothing -> Nothing
             Strict.Just (pos `Strict.And` gap) -> Just (pos, gap)
  return (a (cs Semi.<> csf) ce)

acs :: (HasLoc l, MonadP m) => l -> (l -> EpAnnComments -> GenLocated l a) -> m (GenLocated l a)
acs !l a = do
  !cs <- getCommentsFor (locA l)
  return (a l cs)

acsA :: (HasLoc l, HasAnnotation t, MonadP m)
     => l
     -> (l -> EpAnnComments -> Located a)
     -> m (GenLocated t a)
acsA !l a = do
  !cs <- getCommentsFor (locA l)
  return $ reLoc (a l cs)

ams1 :: MonadP m => Located a -> b -> m (LocatedA b)
ams1 (L l a) b = do
  !cs <- getCommentsFor l
  return (L (EpAnn (spanAsAnchor l) noAnn cs) b)

amsA' :: (NoAnn t, MonadP m) => Located a -> m (GenLocated (EpAnn t) a)
amsA' (L l a) = do
  !cs <- getCommentsFor l
  return (L (EpAnn (spanAsAnchor l) noAnn cs) a)

amsA :: MonadP m => LocatedA a -> [TrailingAnn] -> m (LocatedA a)
amsA (L !l a) bs = do
  !cs <- getCommentsFor (locA l)
  return (L (addAnnsA l bs cs) a)

amsAl :: MonadP m => LocatedA a -> SrcSpan -> [TrailingAnn] -> m (LocatedA a)
amsAl (L l a) loc bs = do
  !cs <- getCommentsFor loc
  return (L (addAnnsA l bs cs) a)

amsr :: MonadP m => Located a -> an -> m (LocatedAn an a)
amsr (L l a) an = do
  !cs <- getCommentsFor l
  return (L (EpAnn (spanAsAnchor l) an cs) a)

-- open and close curly brace
moc, mcc :: Located Token -> AddEpAnn
moc !ll = mj AnnOpenC ll
mcc !ll = mj AnnCloseC ll

-- open and close parens
mop, mcp :: Located Token -> AddEpAnn
mop !ll = mj AnnOpenP ll
mcp !ll = mj AnnCloseP ll

parseModule :: P (Located (CsModule Ps))
parseModule = parseModuleNoHaddock

commentsA :: (NoAnn ann) => SrcSpan -> EpAnnComments -> EpAnn ann
commentsA loc cs = EpAnn (EpaSpan loc) noAnn cs

spanWithComments :: (NoAnn ann, MonadP m) => SrcSpan -> m (EpAnn ann)
spanWithComments l = do
  !cs <- getCommentsFor l
  return (commentsA l cs)

commentsPA :: (NoAnn ann) => LocatedAn ann a -> P (LocatedAn ann a)
commentsPA la@(L l a) = do
  !cs <- getPriorCommentsFor (getLocA la)
  return (L (addCommentsToEpAnn l cs) a)

epTok :: Located Token -> EpToken tok
epTok (L !l a) = EpTok (EpaSpan l)

epUniTok :: Located Token -> EpUniToken tok utok
epUniTok t@(L !l _) = EpUniTok (EpaSpan l) u
  where
    u = if isUnicode t then UnicodeSyntax else NormalSyntax

-- -------------------------------------

addTrailingVbarA :: MonadP m => LocatedA a -> SrcSpan -> m (LocatedA a)
addTrailingVbarA la span = addTrailingAnnA la span AddVbarAnn

addTrailingSemiA :: MonadP m => LocatedA a -> SrcSpan -> m (LocatedA a)
addTrailingSemiA la span = addTrailingAnnA la span AddSemiAnn

addTrailingCommaA :: MonadP m => LocatedA a -> SrcSpan -> m (LocatedA a)
addTrailingCommaA la span = addTrailingAnnA la span AddCommaAnn

addTrailingAnnA
  :: MonadP m
  => LocatedA a -> SrcSpan -> (EpaLocation -> TrailingAnn) -> m (LocatedA a)
addTrailingAnnA (L anns a) ss ta =
  let cs = emptyComments
      anns' = if isZeroWidthSpan ss
                then anns
                else addTrailingAnnToA (ta (srcSpan2e ss)) cs anns
  in return (L anns' a)

-- -------------------------------------

addTrailingDarrowC :: LocatedC a -> Located Token -> EpAnnComments -> LocatedC a
addTrailingDarrowC (L (EpAnn lr (AnnContext _ o c) csc) a) lt cs =
  let u = if (isUnicode lt) then UnicodeSyntax else NormalSyntax
  in L (EpAnn lr (AnnContext (Just (u, glAA lt)) o c) (cs Semi.<> csc)) a

-- -------------------------------------

combineHasLocs :: (HasLoc a, HasLoc b) => a -> b -> SrcSpan
combineHasLocs a b = combineSrcSpans (getHasLoc a) (getHasLoc b)
}
