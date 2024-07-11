{
module CSlash.Parser
  ( parseModule, parseImport
  , parseDeclaration, parseExpression
  , parseTypeSignature
  , parseIdentifier
  , parseType
  ) where

-- base
import Control.Monad (unless, liftM, when, (<=<))
import GHC.Exts
import Data.Maybe (maybeToList)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import qualified Prelude -- for happy-generated code

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
import CSlash.Types.Name.Occurrence (varName, tcClsName, tvName, kvName, occNameFS, mkVarOccFS)
import CSlash.Types.SrcLoc
import CSlash.Types.Basic
import CSlash.Types.Error (CsHint(..))
import CSlash.Types.Fixity
import CSlash.Types.SourceText

import CSlash.Parser.PostProcess
import CSlash.Parser.Lexer
import CSlash.Parser.Annotation
import CSlash.Parser.Errors.Types
import CSlash.Parser.Errors.Ppr ()

import CSlash.Builtin.Types ()

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
  PREFIX_MINUS { L _ ITprefixminus }
  TIGHT_INFIX_AT { L _ ITtightinfixat }
  U_KIND { L _ ITstar }
  A_KIND { L _ ITbullet }
  L_KIND { L _ ITcirc }
  '.' { L _ ITdot }

  '/\\' { L _ ITbiglam }

  '{' { L _ ITvocurly }
  '}' { L _ ITvcculry }
  ';' { L _ ITvsemi }
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
%lexer { (lexer True) } { L _ ITeof }
%tokentype { (Located Token) }

%name parseModuleNoHaddock module
%name parseImport importdecl
%name parseDeclaration topdecl
%name parseExpression exp
%name parseTypeSignature sigdecl
%name parseIdentifier identifier
%name parseType ktype
%%

-----------------------------------------------------------------------------
-- Identifiers; one of the entry points

identifier :: { LocatedN RdrName }
  : qvar { $1 }
  | qcon { $1 }
  | qvarop { $1 }
  | qconop { $1 }
  | '(' ARR_U ')' {% amsr (sLL $1 $> $ getRdrName unrestrictedFunTyCon)
                          (NameAnnUnArrow (Just $ glAA $1) (glAA $2) (Just $ glAA $3) []) }
  | ARR_U {% amsr (sLL $1 $> $ getRdrName unrestrictedFunTyCon)
                  (NameAnnUnArrow Nothing (glAA $1) Nothing []) }
  | '(' ARR_A ')' {% amsr (sLL $1 $> $ getRdrName affineFunTyCon)
                          (NameAnnAffArrow (Just $ glAA $1) (glAA $2) (Just $ glAA $3) []) }
  | ARR_A {% amsr (sLL $1 $> $ getRdrName affineFunTyCon)
                  (NameAnnAffArrow Nothing (glAA $1) Nothing []) }
  | '(' ARR_L ')' {% amsr (sLL $1 $> $ getRdrName linearFunTyCon)
                          (NameAnnLinArrow (Just $ glAA $1) (glAA $2) (Just $ glAA $3) []) }
  | ARR_L {% amsr (sLL $1 $> $ getRdrName linearFunTyCon)
                  (NameAnnLinArrow Nothing (glAA $1) Nothing []) }
    
-----------------------------------------------------------------------------
-- Module Header

module :: { Located (CsModule Ps) }
  : 'module' modid exports 'where' body
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

body :: { ( [TrailingANn]
          , ([LImportDecl Ps], [LCsDecl Ps])
          , EpLayout ) }
  : '{' top close { (fst $2, snd $2, EpVirtualBraces (getVOCURLY $1)) }

top :: { ( [TrailingAnn]
         , ([LImportDecl Ps], [LCsDecl Ps]) ) }
  : semis top1 { (reverse $1, $2) }

top1 :: { ([LImportDecl Ps], [LCsDecl Ps]) }
  : importdecls_semi topdecls_cs_semi { (reverse $1, cvTopDecls $2) }
  | importdecls_semi topdecls_cs { (reverse $1, cvTopDecls $2) }
  | importdecls { (reverse $1, []) }

-----------------------------------------------------------------------------
-- The Export List

exports :: { (LocatedL [LIE Ps]) }
  : '(' exportlist ')' {% amsr (sLL $1 $> (fromOL $ snd $2))
                               (AnnList Nothing (Just $ mop $1) (Just $ mcp $3) (fst $2) []) }

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
  : qcname_ext export_subspec {% do let span = comb2 $1 $>
                                    impExp <- mkModuleImpExp (fst $ unLoc $2) $1 (snd $ unLoc $2)
                                    return $ reLoc $ sL span $ impExp }
  | 'module' modid {% do let span = comb2 $1 $>
                             anchor = glR $1
                         locImpExp <- return (sL span (IEModuleContents [mj AnnModule $1]) #2)
                         return $ reLoc $ locImpExp }

-- included for forward compatibility
export_subspec :: { Located ([AddEpAnn], ImpExpSubSpec) }
  : {- empty -} { sL0 ([], ImpExpAbs) }

qcname_ext :: { LocatedA ImpExpQcSpec }
  : qcname { sL1a $1 (ImpExpQcName $1) }
  | 'type' qcname {% do n <- mkTypeImpExp $2
                        return $ sLLa $1 $> (ImpExpQcType (glAA $1) n) }

qcname :: { LocatedN RdrName }
  : qvar { $1 }

-- qcname_body :: { LocatedN RdrName }
--   : vocurly qcname close { $2 }

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
  : importdecls_semi importdecl semis1 {% do i <- amsAl $2 (comb2 $2 $3) (reverse $ unLoc $3)
                                             return (i : $1) }
  | {- empty -} { [] }

importdecl :: { LImportDecl Ps }
  : 'import' modid optqualified maybeas maybeimpspec
      {% do let mPostQual = unLoc $3
                anns = EpAnnImportDecl
                         { importDeclAnnImport = glAA $1
                         , importDeclAnnQualified = mPostQual
                         , importDeclAnnPackage = Nothing
                         , importDeclAnnAs = fst $4
                         }
                loc = comb5 $1 $2 $3 (snd $4) $5
            fmap reLoc $ acs loc (\ loc cs -> L loc $
              ImportDecl { ideclExt = XImportDeclPass (EpAnn (spanAsAnchor loc) anns cs)
                                                      NoSourceText False
                         , ideclName = $2
                         , ideclAs = unLoc (snd $4)
                         , ideclImportList = unLoc $5 }) }

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
  : '(' importlist ')' {% do es <- amsr (sLL $1 $> $ fromOL $ snd $2)
                                        (AnnList Nothing (Just $ mop $1)
                                                 (Just $ mcp $3) (fst $2) [])
                             return $ sLL $1 $> (Exactly, es) }
  | 'hiding' '(' importlist ')' {% do es <- amse (sLL $1 $> $ fromOL $ snd $3)
                                                 (AnnList Nothing (Just $ mop $2)
                                                          (Just $ mcp $4)
                                                          (mj AnnHiding $1:fst $3) []) }

importlist :: { ([AddEpAnn], OrdList (LIE Ps)) }
  : importlist1 { ([], $1) }
  | {- empty -} { ([], nilOL) }
  | importlist1 ',' {% case $1 of
                        SnocOL hs t -> do
                          t' <- addTrailingCommaA t (gl $2)
                          return ([], snocOL hs t') }
  | ',' { ([mk AnnComma $1], nilOL) }

importlist1 :: { OrdList (LIE Ps) }
  : importlist1 ',' import {% let ls = $1
                              in if isNilOL ls
                                 then return (ls `appOL` $3)
                                 else case ls of
                                        SnocOL hs t -> do
                                          t' <- addTrailingCommaA t (gl $2)
                                          return (snocOL hs t' `appOL` $3) }
  | import { $1 }

import :: { OrdList (LIE Ps) }
  : qcname_ext export_subspec {% fmap (unitOL . reLoc . (sLL $1 $>)) $
                                mkModuleImpExp Nothing (fst $ unLoc $2) $1 (snd $ unLoc $2) }
  | 'module' modid {% fmap (unitOL . reLoc) $
                     return (sLL $1 $> (IEModuleContents (Nothing, [mj AnnModule $1]) $2)) }

-----------------------------------------------------------------------------
-- Fixity Declarations

prec :: { Located (SourceText, Int) }
  : INTEGER { Just (sL1 $1 (getINTEGERs $1, fromInteger (il_value (getINTEGER $1)))) }

infix :: { Located FixityDirection }
  : 'infix' { sL1 $1 InfixN }
  | 'infixl' { sL1 $1 InfixL }
  | 'infixr' { sL1 $1 InfixR }

namespace_spec :: { Located NamespaceSpecifier }
  : 'type' { sL1 $1 $ TypeNamespaceSpecifier (epTok $1) }
  | {- empty -} { sL0 $ NoNamespaceSpecifier }

-----------------------------------------------------------------------------
-- Top-Level Declarations

topdecls :: { OrdList (LCsDecl Ps) }
  : topdecls_semi topdecl { $1 `snocOL` $2 }

topdecls_semi :: { OrdList (LCsDecl Ps) }
  : topdecls_semi topdecl semis1 {% do t <- amsAl $2 (comb2 $2 $3) (reverse $ unLoc $3)
                                       return ($1 `snocOL` t) }
  | {- empty -} { nilOL }

topdecls_cs :: { OrdList (LCsDecl Ps) }
  : topdecls_cs_semi topdecl_cs { $1 `snocOL` $2 }

topdecls_cs_semi :: { OrdList (LCsDecl Ps) }
  : topdecls_cs_semi topdecl_cs semis1 {% do t <- amsAl $2 (comb2 $2 $3) (reverse $ unLoc $3)
                                             return ($1 `snocOL` t) }
  | {- empty -} { nilOL }

topdecl_cs :: { LCsDecl Ps }
  : topdecl {% commentsPA $1 }

-----------------------------------------------------------------------------
topdecl :: { LCsDecl Ps }
  : ty_decl { L (getLoc $1) (ValD noExtField (unLoc $1)) }
  | decl { $1 }


-- Type declarations (toplevel)
--
ty_decl :: { LCsBind Ps }
  : 'type' var '=' ctype {% mkTyFunBind (comb2 $1 $4) $2 $4 [mj AnnType $1, mj AnnEqual $3] }

-----------------------------------------------------------------------------
-- Nested declarations

-- Declarations in binding groups other than classes and instances
--
decls :: { Located ([AddEpAnn], OrdList (LCsDecl Ps)) }
  : decls ';' decl {% if isNilOL (snd $ unLoc $1)
                      then return (sLL $1 $> ( (fst $ unLoc $1) ++ (msemiA $1)
                                             , unitOL $3))
                      else case (snd $ unLoc $1) of
                             SnocOL hs t -> do t' <- addTrailingSemiA t (gl $2)
                                               let this = unitOL $3
                                                   rest = snocOL hs t'
                                                   these = rest `appOL` this
                                               return (rest `seq` this `seq` these `seq`
                                                        (sLL $1 $> (fst $ unLoc $1, these))) }
  | decls ';' {% if isNilOL ( snd $ unLoc $1)
                 then return (sLZ $1 $> ( (fst $ unLoc $1) ++ (msemiA $2)
                                        , snd $ unLoc $1))
                 else case (snd $ unLoc $1) of
                        SnocOL hs t -> do t' <- addTrailingSemiA t (gl $2)
                                          return (sLZ $1 $> ( fst $ unLoc $1
                                                            , snocOL hs t')) }
  | decl { sL1 $1 ([], unitOL $1) }
  | {- empty -} { noLoc ([], nilOL) }

decllist :: { Located (AnnList, Located (OrdList (LCsDecl Ps))) }
  : '{' decls close { L (gl $1) ( AnnList (Just $ glR $2) Nothing Nothing (fst $ unLoc $2) []
                                , sL1 $2 $ snd $ unLoc $2) }

-- Binding groups other than those of class and instance declarations
--
binds :: { Located (CsLocalBinds Ps) }
  : decllist {% do val_binds <- cvBindGroup (unLoc $ snd $ unLoc $1)
                   !cs <- getCommentsFor (gl $1)
                   return (sL1 $1 $ CsValBinds (fixValbindsAnn $ EpAnn
                            (glR $1) (fst $ unLoc $1) cs) val_binds) }

-----------------------------------------------------------------------------
-- Type signatures

sigktype :: { LCsSigType Ps }
  : sigtype { $1 }
  | ctype ':' kind {$ amsA' (sLL $1 $> $ mkCsImplicitSigType $
                             sLLa $1 $> $ CsKindSig [mu AnnColon $2] $1 $3) }

sigtype :: { LCsSigType Ps }
  : ctype { csTypeToCsSigType $1 }

-----------------------------------------------------------------------------
-- Types

forall_telescope :: { Located (CsForAllTelescope Ps) }
  : 'forall' tv_bndrs '.' {% do hintExplicitForall $1
                                acs (comb2 $1 $>) (\loc cs -> (L loc $
                                  mkCsForAllInvisTele (EpAnn (glEE $1 $>)
                                                             ( mu AnnForall $1
                                                             , mu AnnDot $3) cs) $2)) }

ktype :: { LCsType Ps }
  : ctype { $1 }
  | ctype ':' kind {% amsA' (sLL $1 $> $ CsKindSig [mu AnnColon $2] $1 $3) }

ctype :: { LCsType Ps }
  : context '=>' ctype1 {% acsA (comb2 $1 $>) (\ loc cs -> (L loc $
                             CsQualTy { cst_ctxt = addTrailingDarrowC $1 $2 cs
                                      , cst_xqual = noExtField
                                      , cst_body = $3 })) }
  | ctype1 { $1 }

ctype1 :: { LCsType Ps }
  : forall_telescope ctype1 { sLLa $1 $> $ CsForAllTy { cst_tele = unLoc $1
                                                      , cst_xforall = noExtField
                                                      , cst_body = $2 } }
  | type { $1 }

context :: { LCsContext Ps }
  : context1 { L (getLoc $1) (reverse (unLoc $1)) }

context1 :: { LCsContext Ps }
  : '(' context ')' {% amsr (sLL $1 $> (unLoc $2))
                            (NameAnn NameParens (glAA $1) (glAA $2) (glAA $3) []) }
  | context ',' kvrel {% case unLoc $1 of
                           (h:t) -> do h' <- addTrailingCommA h (gl $2)
                                       return (sLL $1 $> ($3 : (h':t))) }
  | kvrel { [$1] }

kvrel :: { LCsKdRel Ps }
  : varid VARSYM varid {% mkKvRel $1 $2 $3 }

type :: { LCsType Ps }
  : btype %shift { $1 }
  | btype ARR_U ctype {% amsA' (sLL $1 $> $ CsFunTy noExtField
                                                    (CsArrow (epUniTok $2) (CsUKd noExtField))
                                                    $1 $3) }
  | btype ARR_A ctype {% amsA' (sLL $1 $> $ CsFunTy noExtField
                                                    (CsArrow (epUniTok $2) (CsAKd noExtField))
                                                    $1 $3) }
  | btype ARR_L ctype {% amsA' (sLL $1 $> $ CsFunTy noExtField
                                                    (CsArrow (epUniTok $2) (CsLKd noExtField))
                                                    $1 $3) }

btype :: { LCsType Ps }
  : infixtype {% runPV $1 }

infixtype :: { forall b. DisambTD b => PV (LocatedA b) }
  : ftype %shift { $1 }
  | ftype tyop infixtype { $1 >>= \ $1 ->
                           $3 >>= \ $3 ->
                             let (op, prom) = $2
                             in mkCsOpTyPV prom $1 op $3 }

ftype :: { forall b. DisambTD b => PV (LocatedA b) }
  : atype { mkCsAppTyHeadPV $1 }
  | tyop { failOpFewArgs (fst $1) }
  | ftype atype { $1 >>= \ $1 -> mkCsTyAppTyPV $1 $2 }

tyop :: { LocatedN RdrName }
  : qtyconop { $1 }
  | tyvarop { $1 }

atype :: { LCsType Ps }
  : ntgtycon {% amsA' (sL1 $1 (CsTyVar [] $1)) }
  | tyvar %shift {% amsA' (sL1 $1 (CsTyVar [] $1)) }
  | '\\' tyargpats '->' type { mkCsTyLamTy (comb2 $1 $>)
                                 (sLLl $1 $>
                                  [sLLa $1 $> $ Match
                                                { m_ext = []
                                                , m_ctxt = TyLamTyAlt
                                                , m_pats = L (listLocation $2) $2
                                                , m_grhss = unguardedGRHSs
                                                              (comb2 $3 $4) $4
                                                              (EpAnn (glR $3)
                                                                     (GrhsAnn Nothing
                                                                              (mu AnnRarrow $3))
                                                                     emptyComments) }])
                                 [mj AnnLam $1] }
  | '(' ')' {% amsA' . sLL $1 $> =<< (mkTupleSyntaxTy (glR $1) [] (glR $>)) }
  | '(' comma_types2 ')' {% amsA' (sLL $1 $> $
                                     CsTupleTy (AnnParen AnnParens (glAA $1) (glAA $2)) $2) }
  | '(' bar_types2 ')' {% amsA' (sLL $1 $> $ CsSumTy (AnnParen AnnParens (glAA $1) (glAA $2)) $2) }
  | '(' ktype ')' {% amsA' (sLL $1 $> $ CsParTy (AnnParen AnnParens (glAA $1) (glAA $3)) $2) }
  -- This is an error that we handle in the renamer
  | QVARID {% let qname = mkQual tvName (getQVARID $1)
              in amsA' (sL1 $1 (CsTyVar p[ (sL1n $1 $ qname)))) }

comma_types2 :: { [LCsType Ps] }
  : ktype ',' ktype {% do h <- addTrailingCommaA $1 (gl $2)
                          return [h, $3] }
  | ktype ',' comma_types2 {% do h <- addTrailingCommaA $1 (gl $2)
                                 return (h : $3) }

bar_types2 :: { [LCsType Ps] }
  : ktype '|' ktype {% do h <- addTrailingVbarA $1 (gl $2)
                          return [h, $3] }
  | ktype '|' bar_types2 {% do h <- addTrailingVbarA $1 (gl $2)
                               return (h : $3) }

tv_bndrs :: { [LCsTyVarBndr Ps] }
  : tv_bndr { [$1] }
  | tv_bndrs1 { $1 }

tv_bndrs1 :: { [LCsTyVarBndr Ps] }
  : tv_bndr_parens tv_bndrs { $1 : $2 }
  | {- empty -} { [] }

tv_bndr :: { LCsTyVarBndr Ps }
  : tyvar ':' kind {% amsA' (sLL $1 $> (KindedTyVar [mu AnnColon] $1 $3)) }

tv_bndr_parens :: { LCsTyVarBndr Ps }
  : '(' tyvar ':' kind ')' {% amsA' (sLL $1 $> (KindedTyVar [mop $1, mu AnnColon, mcp $5] $2 $4)) }

-----------------------------------------------------------------------------
-- Kinds

kind :: { LCsKind Ps }
  : akind { $1 }
  | akind '->' akind {% amsA' (sLL $1 $> $ CsFunKd noExtField $1 $3) }

akind :: { LCsKind Ps }
  : U_KIND { sL1a $1 (CsUKd noExtField) }
  | A_KIND { sL1a $1 (CsAKd noExtField) }
  | L_KIND { sL1a $1 (CsAKd noExtField) }
  | varid {% amsA' (sL1 $1 (CsKdVar [] $1)) }
  | '(' kind ')' {% amsA' (sLL $1 $> $ CsParKd (AnnParen AnnParens (glAA $1) (glAA $3)) $2) }

-----------------------------------------------------------------------------
-- Datatype declarations

-----------------------------------------------------------------------------
-- Value definitions

decl :: { LCsDecl Ps }
  : sigdecl { $1 }
  | var '=' exp {% amsA' $ sLL $1 $> $ ValD noExtField $
                     FunBind (mj AnnEqual $2) $1 $3 }
                -- {% runPV (unECP $2) >>= \ ($2 :: LCsExpr Ps) ->
                --      mkFunBind (comb2 $1 $>) $1 $3 (mj AnnEqual $2) }

sigdecl :: { LCsDecl Ps }
  : var ':' sigtype {% amsA' $ sLL $1 $> $ SigD noExtField $
                         TypeSig (AnnSig (mu AnnColon $2) []) $1 $3 }

  | infix prec namespace_spec op
      {% do mbPrecAnn <- traverse (\ l2 -> do checkPrecP l2 $4
                                              pure (mj AnnVal l2)) $2
            let (fixText, fixPrec) = (fst $ unLoc l2, snd $ unLoc l2)
            amsA' (sLL $1 $> $ SigD noExtField
                   (FixSig (mj AnnInfix $1 : maybeToList mbPrecAnn fixText)
                           (FixitySig (unLoc $3) (unLoc $4) (Fixity fixPrec (unLoc $1))))) }

-----------------------------------------------------------------------------
-- Expressions

exp :: { ECP }
  : infixexp %shift { $1 }

infixexp :: { ECP }
  : exp10 { $1 }
  | infixexp qop exp10 { ECP $
                         superInfixOp $
                         $2 >>= \ $2 ->
                         unECP $1 >>= \ $1 ->
                         unECP $3 >>= \ $3 ->
                         (mkCsOpAppPV (comb2 $1 $3) $1 $2 $3) }

exp10 :: { ECP }
  : fexp %shift { $1 }

optSemi :: { (Maybe EpaLocation, Bool) }
  : ';' { (msemim $1, True) }
  | {- empty -} { (Nothing, False) }

fexp :: { ECP }
  : fexp aexp { ECP $ superFunArg $
                      unECP $1 >>= \ $1 ->
                      unECP $2 >>= \ $2 ->
                      spanWithComments (comb2 $1 $>) >>= \ l ->
                      mkCsAppPV l $1 $2 }
  | fexp atype { ECP $ unECP $1 >>= \ $1 ->
                       mkCsAppTypePV (noAnnSrcSpan $ comb2 $1 $>) $1 $2 }
  | aexp { $1 }

aexp :: { ECP }
  : qvar TIGHT_INFIX_AT aexp { ECP $ unECP $3 >>= \ $3 ->
                                     mkCsAsPatPV (comb2 $1 $>) $1 (epTok $2) $3 }
  | PREFIX_MINUS aexp { ECP $ unECP $2 >>= \ $2 ->
                              mkCsNegAppPV (comb2 $1 $>) $2 [mj AnnMinus $1] }
  | 'let' binds 'in' exp { ECP $ unECP $4 >>= \ $4 ->
                                 mkCsLecPV (comb2 $1 $>) (epTok $1) (unLoc $2) (epTok $3) $4 }
  | '\\' argpats '->' exp { ECP $ unECP $4 >>= \ $4 ->
                                  mkCsLamPV (comb2 $1 $>)
                                    (sLLl $1 $>
                                     [sLLa $1 $> $ Match
                                                   { m_ext = []
                                                   , m_ctxt = LamAlt
                                                   , m_pats = L (listLocation $2) $2
                                                   , m_grhss = unguardedGRHSs
                                                                 (comb2 $3 $4) $4
                                                                 (EpAnn (glR $3)
                                                                        (GrhsAnn Nothing
                                                                                 (mu AnnRarrow $3))
                                                                        emptyComments) }])
                                    [mj AnnLam $1] }
  | '/\\' tyargpats '->' exp { ECP $ unECP $4 >>= \ $4 ->
                                 mkCsTyLamPV (comb2 $1 $>)
                                     (sLLl $1 $>
                                      [sLLa $1 $> $ Match
                                                    { m_ext = []
                                                    , m_ctxt = TLamAlt
                                                    , m_pats = L (listLocation $2) $2
                                                    , m_grhss = unguardedGRHSs
                                                                 (comb2 $3 $4) $4
                                                                 (EpAnn (glR $3)
                                                                        (GrhsAnn Nothing
                                                                                 (mu AnnRarrow $3))
                                                                        emptyComments) }])
                                     [mj AnnTyLam $1] }
  | 'if' exp optSemi 'then' exp optSemi 'else' exp
      {% runPV (unECP $2) >>= \ ($2 :: LCsExpr Ps) ->
           return $ ECP
             unECP $5 >>= \ $5 ->
             unECP $8 >>= \ $8 ->
             mkCsIfPV (comb2 $1 $>) $2 (snd $3) $5 (snd $6) $8
                      (AnnsIf
                       { aiIf = glAA $1
                       , aiThen = glAA $4
                       , aiElse = glAA $7
                       , aiThenSemi = fst $3
                       , aiElseSemi = fst $6 }) }
  | 'if' ifgdpats {% fmap ecpFromExp $
                     amsA' (sLL $1 $> $ CsMultiIf (mj AnnIf $1:(fst $ unLoc $2))
                                                  (reverse $ snd $ unLoc $2)) }
  | 'case' exp 'of' altslist(pats1) {% runPV (unECP $2) >>= \ ($2 :: LCsExpr Ps) ->
                                       return $ ECP $
                                       $4 >>= \ $4 ->
                                       mkCsCasePV (comb3 $1 $3 $4) $2 $4
                                                  (EpAnnCsCase (glAA $1) (glAA $3) []) }
  | aexp1 { $1 }

aexp1 :: { ECP }
  : aexp2 { $1 }

aexp2 :: { ECP }
  : qvar { ECP $ mkCsVarPV $! $1 }
  | qcon { ECP $ mkCsVarPV $! $1 }
  | literal { ECP $ mkCsLitPV $! $1 }
  | INTEGER { ECP $ mkCsOverLitPV (sL1a $1 $ mkCsIntegral (getINTEGER $1)) }
  | RATIONAL { ECP $ mkCsOverLitPV (sL1a $1 $ mkCsFractional (getRATIONAL $1)) }
  | '(' texp ')' { ECP $ unECP $2 >>= \ $2 ->
                         mkCsParPV (comb2 $1 $>) (epTok $1) $2 (epTOk $3) }
  | '(' tup_exprs ')' { ECP $ 2 >>= \ $2 ->
                              mkSumOrTuplePV (noAnnSrcSpan $ comb2 $1 $>) $2 [mop $1, mcp $3] }
  | '_' { ECP $ mkCsWildCardPV (getLoc $1) }

-----------------------------------------------------------------------------
-- Tuple expressions

texp :: { ECP }
  : exp { $1 }
  | infixexp qop {% runPV (unECP $1) >>= \ $1 ->
                    runPV (rejectPragmaPV $1) >>
                    runPV $2 >>= \ $2 ->
                    return $ ecpFromExp $
                    sLLa $1 $> $ SectionL noExtField $1 (n2l $2) }
  | qopm infixexp { ECP $ superInfixOp $
                          unECP $2 >>= \ $2 ->
                          $1 >>= \ $1 ->
                          mkCsSectionR_PV (comb2 $1 $>) (n2l $1) $2 }

tup_exprs :: { forall b. DisambECP b => PV (SumOrTuple b) }
  : texp commas_tup_tail { unECP $1 >>= \ $1 ->
                           $2 >>= \ $2 -> do
                             t <- amsA $1 [AddCommaAnn (srcSpan2e $ fst $2)]
                             return (Tuple (Right t : snd $2)) }
  | commas tup_tail { $2 >>= \ $2 -> 
                        let cos = map (\ ll -> (Left (EpAnn (spanAsAnchor ll) True emptyComments)))
                                      (fst $1)
                        in return (Tuple (cos ++ $2)) }
  | texp bars { unECP $1 >>= \ $1 -> return $
                (Sum 1 (snd $2 + 1) $1 [] (map srcSpan2e $ fst $2)) }
  | bars texp bars0 { unECP $ 2 >>= \$2 -> return $
                      (Sum (snd $1 + 1) (snd $1 + snd $3 + 1) $2
                        (map srcSpan2e $ fst $1)
                        (map srcSpan2e $ fst $3)) }

commas_tup_tail :: { forall b. DisambECP b => PV (SrcSpan, [Either (EpAnn Bool) (LocatedA b)]) }
  : commas tup_tail { $2 >>= \ $2 ->
                        let cos = map (\ l -> (Left (EpAnn (spanAsAnchor l) True emptyComments)))
                                      (tail $ fst $1)
                        in return ((head $ fst $1, cos ++ $2)) }

tup_tail :: { forall b. DisambECP b => PV [Either (EpAnn BOol) (LocatedA b)] }
  : texp commas_tup_tail { unECP $1 >>= \ $1 ->
                           $2 >>= \ $2 -> do
                             t <- amsA $1 [AddCommaAnn (srcSpan2e $ fst $2)]
                             return (Right t : snd $2) }
  | texp { unECP $1 >>= \ $1 -> return [Right $1] }
  | {- empty -} %shift { return [Left noAnn] }

-----------------------------------------------------------------------------
-- Guards

guardquals :: { Located [LStmt Ps (LCsExpr Ps)] }
  : guardquals1 { L (getLoc $1) (reverse (unLoc $1)) }

guardquals1 :: { Located [LStmt Ps (LCsExpr Ps)] }
  : guardquals1 ',' qual {% runPV $3 >>= \ $3 ->
                            case unLoc $1 of
                              (h:t) -> do
                                h' <- addTrailingCommA h (gl $2)
                                return (sLL $1 $> ($3 : (h':t))) }
  | qual {% runPV $1 >>= \ $1 -> return $ sL1 $1 [$1] }

-----------------------------------------------------------------------------
-- Case alternatives

altslist(PATS) :: { forall b. DisambECP b => PV (LocatedL [LMatch Ps (LocatedA b)]) }
  : '{' alts(PATS) close { $2 >>= \ $2 -> amsr
                             (sLL $1 $> (reverse (snd $ unLoc $2)))
                             (AnnList (Just $ glR $2) (Just $ moc $1)
                                      (Just $ mcc $3) (fst $ unLoc $2) []) }
  | '{' close { return $ noLocA [] }

alts(PATS) :: { forall b. DisambECP b => PV (Located ([AddEpAnn], [LMatch Ps (LocatedA b)])) }
  : alts1(PATS) { $1 >>= \ $1 -> return $
                  sL1 $1 (fst $ unLoc $1, snd $ unLoc $1) }
  | ';' alts(PATS) { $2 >>= \ $2 -> return $
                     sLL $1 $> ( ((mz AnnSemi $1) ++ (fst $ unLoc $2) )
                               , snd $ unLoc $2) }

alts1(PATS) :: { forall b. DisambECP b => PV (Located ([AddEpAnn], [LMatch Ps (LocatedA b)])) }
  : alts1(PATS) ';' alt(PATS) { $1 >>= \ $1 ->
                                $3 >>= \ $3 ->
                                  case snd $ unLoc $1 of
                                    [] -> return (sLL $1 $> ( (fst $ unLoc $1) ++ (mz AnnSemi $2)
                                                            , [$3] )
                                    (h:t) -> do
                                      h' <- addTrailingSemiA h (gl $2)
                                      return (sLZ $1 $> (fst $ unLoc $1, h':t))) }
  | alt(PATS) { $1 >>= \ $1 -> return $ sL1 $1 ([], [$1]) }

alt(PATS) :: { forall b. DisambECP b => PV (LMatch Ps (LocatedA b)) }
  : PATS alt_rhs { $2 >>= \ $2 ->
                   amsA' (sLLAsl $1 $>
                          (Match { m_ext = []
                                 , m_ctxt = CaseAlt
                                 , m_pats = L (listLocation $1) $1
                                 , m_grhss = unLoc $2 })) }

alt_rhs :: { forall b. DisambECP b => PV (Located (GRHSs Ps (LocatedA b))) }
  : ralt { $1 >>= \ alt -> let L l a = alt in acs l (\ loc cs -> L loc (GRHSs cs a)) }
             
ralt :: { forall b. DisambECP b => PV (Located [LGRHS Ps (LocatedA b)]) }
  : '->' exp { unECP $2 >>= \ $2 ->
               acs (comb2 $1 $>) (\ loc cs -> L loc (unguardedRHS
                                                     (EpAnn (spanAsAnchor $ comb2 $1 $2)
                                                            (GrhsAnn Nothing (mu AnnRarrow $1))
                                                            cs)
                                                      (comb2 $1 $2) $2)) }
  | gdpats { $1 >>= \ gdpats -> return $ sL1 gdpats (reverse (unLoc gdpats)) }

gdpats :: { forall b . DisambEcp b => PV (Located [LGRHS Ps (LocatedA b)]) }
  : gdpats gdpat { $1 >>= \ gdpats ->
                   $2 >>= \ gdpat ->
                   return $ sLL gdpats gdpat ( gdpat : unLoc gdpats) }
  | gdpat { $1 >>= \ gdpat -> return $ sL1 gdpat [gdpat] }

ifgdpats :: { Located ([AddEpAnn], [LGRDS Ps (LCsExpr Ps)]) }
  : gdpats close {% runPV $1 >>= \ $1 -> return $ sL1 $1 ([], unLoc $1) }

gdpat :: { forall b. DisambECP b => PV (LGRHS Ps (LocatedA b)) }
  : '|' guardquals '->' exp { unECP $4 >>= \ $4 ->
                              acsA (comb2 $1 $>)
                                   (\ loc cs -> sL loc $
                                        GRHS (EpAnn (glEE $1 $>)
                                                    (GrhsAnn (Just $ glAA $1) (mu AnnRarrow $3))
                                                    cs)
                                             (unLoc $2) $4) }

pat :: { LPat Ps }
  : exp {% (checkPattern <=< runPV (unECP $1)) }

pats1 :: { [LPat Ps] }
  : pat { [$1] }

bindpat :: { LPat Ps }
  : exp {% checkPattern_details incompleteDoBlock (unECP $1) }

argpat :: { LPat Ps }
  : apat { $1 }

argpats :: { [LPat Ps] }
  : argpat argpats { $1 : $2 }
  | argpat { [$1] }

apat :: { LPat Ps }
  : aexp {% (checkPattern <=< runPV) (unECP $1) }

tyargpat :: { LPat Ps }
  : atypat { $1 }

tyargpats :: { [LPat Ps] }
  : tyargpat tyargpats { $1 : $2 }
  | tyargpat { [$1] }

atypat :: { LPat Ps }
  : atype {% checkTyPattern $1 }

-----------------------------------------------------------------------------
-- Statement sequences

-- stmts are for do notation or arrow notation afaik
-- stmtlist :: { forall b. DisambECP b => PV (LocatedL [LocatedA (Stmt Ps (LocatedA b))]) }
--   : '{' stmts close { $2 >>= \ $2 -> amsr
--                       (L (stmtsLoc $2) (reverse $ snd $ unLoc $2))
--                       (AnnList (stmtsAnchor $2) Nothing Nothing (fromOL $ fst $ unLoc $2) []) }

-- stmts :: { forall b. DisambECP b => PV (Located (OrdList AddEpAnn, [LStmt Ps (LocatedA b)])) }
--   : stmts ';' stmt { $1 >>= \ $1 ->
--                      $3 >>= \ ($3 :: LStmt Ps (LocatedA b)) ->
--                      case (snd $ unLoc $1) of
--                        [] -> return (sLL $1 $> ( (fst $ unLoc $1) `snocOL` (mk AnnSemi $2)
--                                                , $3 : (snd $ unLoc $1)))
--                        (h:t) -> do h' <- addTrailingSemiA h (gl $2)
--                                    return $ sLL $1 $> (fst $ unLoc $1, $3 : (h':t)) }
--   | stmts ';' { $1 >>= \ $1 ->
--                 case (snd $ unLoc $1) of
--                   [] -> return (sLZ $1 $> ( (fst $ unLoc $1) `snocOL` (mj AnnSemi $1)
--                                           , snd $ unLoc $1))
--                   (h:t) -> do h' <- addTrailingSemiA h (gl $2)
--                               return $ sLZ $1 $> (fst $ unLoc $1, h':t) }
--   | stmt { $1 >>= \ $1 -> return $ sL1 $1 (nilOL, [$1]) }
--   | {- empty -} { return $ noLoc (nilOL, []) }

-- maybe_stmt :: { Maybe (LStmt Ps (LCsExpr Ps)) }
--   : stmt {% fmap Just (runPV $1) }
--   | {- empty -} { Nothing }

-- e_stmt :: { LStmt Ps (LCsExpr Ps) }
--   : stmt {% runPV $1 }

-- stmt :: { forall b. DisambECP b => PV (LStmt Ps (LocatedA b)) }
--   : qual { $1 }

-- a special stmt used in guards
qual :: { forall b. DisambECP b => PV (LStmt Ps (LocatedA b)) }
  : bindpat '<-' exp { unECP $3 >>= \$2 ->
                       amsA' (sLL $1 $> $ mkPsBindStmt [mu AnnLarrow $2] $1 $3) }
  | exp { unECP $1 >>= \ $1 -> return $ sL1a $1 $ mkBodyStmt $1 }
  | 'let' binds { amsA' (sLL $1 $> $ mkLetStmt [mj AnnLet $1] (unLoc $2)) }

-----------------------------------------
-- Data constructors

qcon :: { LocatedN RdrName }
  : gen_qcon { $1 }
  | sysdcon { L (getLoc $1) $ nameRdrName (dataConName (unLoc $1)) }

gen_qcon :: { Located RdrName }
  : qconid { $1 }
  | '(' qconsym ')' {% amsr (sLL $1 $> (unLoc $2))
                            (NameAnn NameParens (glAA $1) (glAA $2) (glAA $3) []) }

con :: { LocatedN RdrName }
  : conid { $1 }
  | '(' consym ')' {% amsr (sLL $1 $> (unLoc $2))
                           (NameAnn NameParens (glAA $1) (glAA $2) (glAA $3) []) }
  | sysdcon { L (getLoc $1) $ nameRdrName (dataConName (unLoc $1)) }

sysdcon_nolist :: { LocatedN DataCon }
  : '(' commas ')' {% amsr (sLL $1 $> $ tupleDataCon (snd $2 + 1))
                           (NameAnnCommas NameParens (glAA $1) (map srcSpan2e (fst $2))
                                          (glAA $3) []) }

sysdcon :: { LocatedN DataCon }
  : sysdcon_nolist { $1 }
  | '(' ')' {% amsr (sLL $1 $> unitDataCon)
                    (NameAnnOnly NameParens (glAA $1) (glAA $2) []) }

conop :: { LocatedN RdrName }
  : consym { $1 }
  | '`' conid '`' {$ amsr (sLL $1 $> (unLoc $2))
                          (NameAnn NameBackquotes (glAA $1) (glAA $2) (glAA $3) []) }

qconop :: { LocatedN RdrName }
  : qconsym { $1 }
  | '`' qconid '`' {% amsr (sLL $1 $> (unLoc $2))
                           (NameAnn NameBackquotes (glAA $1) (glAA $2) (glAA $3) []) }

----------------------------------------------------------------------------
-- Type constructors

gtycon :: { LocatedN RdrName }
  : ntgtycon { $1 }
  | '(' ')' {% amsr (sLL $1 $> $ getRdrName unitTyCon)
                    (NameAnnOnly NameParens (glAA $1) (glAA $2) []) }

ntgtycon :: { LocatedN RdrName }
  : oqtycon { $1 }
  | '(' commas ')' {% do n <- mkTupleSyntaxTycon (snd $2 + 1)
                         amsr (sLL $1 $> n) (NameAnnCommas NameParens (glAA $1)
                                                           (map srcSpan2e (fst $2))
                                                           (glAA $3) []) }
  | '(' bars ')' {% amsr (sLL $1 $> $ (getRdrName (sumTyCon (snd $2 + 1))))
                         (NameAnnBars NameParens (glAA $1) (map srcSpan2e (fst $2)) (glAA $3) []) }
  | '(' ARR_U ')' {% amsr (sLL $1 $> $ getRdrName unrestrictedFunTyCon)
                          (NameAnnUnArrow (Just $ glAA $1) (glAA $2)
                                          (Just $ glAA $3) []) }
  | '(' ARR_A ')' {% amsr (sLL $1 $> $ getRdrName affineFunTyCon)
                          (NameAnnAffArrow (Just $ glAA $1) (glAA $2)
                                           (Just $ glAA $3) []) }
  | '(' ARR_L ')' {% amsr (sLL $1 $> $ getRdrName linearFunTyCon)
                          (NameAnnLinArrow (Just $ glAA $1) (glAA $2)
                                           (Just $ glAA $3) []) }

oqtycon :: { LocatedN RdrName }
  : qtycon { $1 }
  | '(' qtyconsym ')' {% amsr (sLL $1 $> (unLoc $2))
                              (NameAnn NameParens (glAA $1) (glAA $2) (glAA $3) []) }

qtyconop :: { LocatedN RdrName }
  : qtyconsym %shift { $1 }
  | '`' qtycon '`' {% amsr (sLL $1 $> (unLoc $2))
                           (NameAnn NameBackquotes (glAA $1) (glAA $2) (glAA $3) []) }

qtycon :: { LocatedN RdrName }
  : QCONID { sL1n $1 $! mkQual tcClsName (getQCONID $1) }
  | tycon { $1 }

tycon :: { LocatedN RdrName }
  : CONID { sL1n $1 $! mkUnqual tcClsName (getCONID $1) }

qtyconsym :: { LocatedN RdrName }
  : QCONSYM { sL1n $1 $! mkQual tcClsName (getQCONSYM $1) }
  | QVARSYM { sL1n $1 $! mkQual tcClsName (getQVARSYM $1) }
  | tyconsym { $1 }

tyconsym :: { LocatedN RdrName }
  : CONSYM { sL1n $1 $! mkUnqual tcClsName (getCONSYM $1) }
  | VARSYM { sL1n $1 $! mkUnqual tcClsName (getVARSYM $1) }

otycon :: { LocatedN RdrName }
  : tycon { $1 }
  | '(' tyconsym ')' {% amsr (sLL $1 $> (unLoc $2))
                             (NameAnn NameParens (glAA $1) (glAA $2) (glAA $3) []) }

-----------------------------------------------------------------------------
-- Operators

op :: { LocatedN RdrName }
  : varop { $1 }
  | conop { $1 }
  | ARR_U {% amsr (sLL $1 $> $ getRdrName unrestrictedFunTyCon)
                  (NameAnnUnArrow Nothing (glAA $1) Nothing []) }
  | ARR_A {% amsr (sLL $1 $> $ getRdrName affineFunTyCon)
                  (NameAnnAffArrow Nothing (glAA $1) Nothing []) }
  | ARR_L {% amsr (sLL $1 $> $ getRdrName linearFunTyCon)
                  (NameAnnLinArrow Nothing (glAA $1) Nothing []) }

varop :: { LocatedN RdrName }
  : varsym { $1 }
  | '`' varid '`' {% amsr (sLL $1 $> (unLoc $2))
                          (NameAnn NameBackquotes (glAA $1) (glAA $2) (glAA $3) []) }

qop :: { forall b. DisambInfixOp b => PV (LocatedN b) }
  : qvarop { mkCsVarOpPV $1 }
  | qconop { mkCsConOpPV $1 }

qopm :: { forall b. DisambInfixOp b => PV (LocatedN b) }
  : qvaropm { mkCsVarOpPV $1 }
  | qconop { mkCsConOpPV $1 }

qvarop :: { LocatedN RdrName }
  : qvarsym { $1 }
  | '`' qvarid '`' {% amsr (sLL $1 $> (unLoc $2))
                           (NameAnn NameBackquotes (glAA $1) (glAA $2) (glAA $3) []) }

qvaropm :: { LocatedN RdrName }
  : qvarsym { $1 }
  | '`' qvarid '`' {% amsr (sLL $1 $> (unLoc $2))
                           (NameAnn NameBackquotes (glAA $1) (glAA $2) (glAA $3) []) }

-----------------------------------------------------------------------------
-- Type variables

tyvar :: { LocatedN RdrName }
  : tyvarid { $1 }

tyvarop :: { LocatedN RdrName }
  : '`' tyvarid '`' {% amsr (sLL $1 $> (unLoc $2))
                            (NameAnn NameBackquotes (glAA $1) (glAA $2) (glAA $3) []) }

tyvarid :: { LocatedN RdrName }
  : VARID { sL1n $1 $! mkUnqual tvName (getVARID $1) }

-----------------------------------------------------------------------------
-- Variables

var :: { LocatedN RdrName }
  : varid { $1 }
  | '(' varsym ')' {% amsr (sLL $1 $> (unLoc $2))
                           (NameAnn NameParens (glAA $1) (glAA $2) (glAA $3) []) }

qvar :: { LocatedN RdrName }
  : qvarid { $1 }
  | '(' varsym ')' {% amsr (sLL $1 $> (unLoc $2))
                           (NameAnn NameParens (glAA $1) (glAA $2) (glAA $3) []) }
  | '(' qvarsym1 ')' {% amsr (sLL $1 $> (unLoc $2))
                             (NameAnn NameParens (glAA $1) (glAA $2) (glAA $3) []) }
  
qvarid :: { LocatedN RdrName }
  : varid %shift { $1 } -- conflict with kvrel
  | QVARID { sL1n $1 $! mkQual varName (getQVARID $1) }

varid :: { LocatedN RdrName }
  : VARID { sL1n $1 $! mkUnqual varName (getVARID $1) }

qvarsym :: { LocatedN RdrName }
  : varsym { $1 }
  | qvarsym1 { $1 }

qvarsym1 :: { LocatedN RdrName }
  : QVARSYM { sL1n $1 $ mkQual varName (getQVARSYM $1) }

varsym :: {LocatedN RdrName }
  : VARSYM { sL1n $1 $ mkUnqual varName (getVARSYM $1) }
  | special_sym { sL1n $1 $ mkUnqual varName (unLoc $1) }

special_sym :: { Located FastString }
  : '.' { sL1 $1 (fsLit ".") }

-----------------------------------------------------------------------------
-- Data constructors

qconid :: { LocatedN RdrName }
  : conid { $1 }
  | QCONID { sL1n $1 $! mkQual dataName (getQCONID $1) }

conid :: { LocatedN RdrName }
  : CONID { sL1n $1 $ mkUnqual dataName (getCONID $1) }

qconsym :: { LocatedN RdrName }
  : consym { $1 }
  | QCONSYM { sL1n $1 $ mkQual dataName (getQCONSYM $1) }

consym :: { LocatedN RdrName }
  : CONSYM { sL1n $1 $ mkUnqual dataName (getCONSYM $1) }

-----------------------------------------------------------------------------
-- Literals

literal :: { Located (CsLit Ps) }
  : CHAR { sL1 $1 $ CsChar (getCHARs $1) $ getCHAR $1 }
  | STRING { sL1 $1 $ CsString (getSTRINGs $1) }

-----------------------------------------------------------------------------
-- Layout

close :: { () }
  : '}' { () }
  | error {% popContext }

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
getCHAR (L _ (ITchar _ x)) = x
getSTRING (L _ (ITstring _ x)) = x
getINTEGER (L _ (ITinteger x)) = x
getRATIONAL (L _ (ITrational x)) = x
getVOCURLY (L (RealSrcSpan l _) ITvocurly) = srcSpanStartCol l

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
comb2 :: (HasLoc a, HasLoc b) => a -> b - SrcSpan
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
sLL :: (hasLoc a, HasLoc b) => a -> b -> c -> Located c
sLL !x !y = sL (comb2 x y)

{-# INLINE sLLa #-}
sLLa :: (HasLoc a, HasLoc b, NoAnn t) => a -> b -> c -> LocatedAn t c
sLLa !x !y = sL (noAnnSrcSpan $ comb2 x y)

{-# INLINE sLLl #-}
sLLl :: (HasLoc a, HasLoc b) => a -> b -> c -> LocatedL c
sLLl !x !y = sL (noAnnSrcSpan $ comb2 x y)

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
msemi !l = is isZeroWidthSpan (gl l) then [] else [AddSemiAnn (srcSpan2e $ gl l)]

msemiA :: Located e -> [AddEpAnn]
msemiA !l = if isZeroWidthSpan (gl l) then [] else [AddEpAnn AnnSemi (srcSpan2e $ gl l)]

msemim :: Located e -> Maybe EpaLocation
msemim !l = if isZeroWidthSpan (gl l) then Nothing else Just (srcSpan2e $ gl l)

mu :: AnnKeywordId -> Located Token -> AddEpAnn
mu !a lt@(L l t) = AddEpAnn (tuUnicodeAnn a lt) (srcSpan2e l)

toUnicodeAnn :: AnnKeywordId -> Located Token -> AnnKeywordId
toUnicodeAnn !a !t = if isUnicode t then unicodeAnn a else a

toUnicode :: Located Token -> IsUnicodeSyntax
toUnicode t = is isUnicode t then UnicodeSyntax else NormalSyntax

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

acsFinal :: (EpaAnnComments -> Maybe (RealSrcSpan, RealSrcSpan) -> Located a) -> P (Located a)
acsFinal a = do
  let (L l _) = a emptyComments Nothing
  !cs <- getCommentsFor l
  csf <- getFinalCommentsFor l
  meof <- getEofPos
  let cs = case meof of
             Strict.Nothing -> Nothing
             Strict.Just (pos `String.And` gap) -> Just (pos, gap)
  return (a, (cs Semi.<> csf) ce)

acs :: (HasLoc l, MonadP m) => l -> (l -> EpAnnComments -> GenLocated l a) -> m (GenLcoated l a)
acs !l a = do
  !cs <- getCommentsFor (locA l)
  return (a l cs)

acsA :: (HasLoc l, HasAnnotation t, MonadP m)
     => l
     -> (l -> EpaAnnComments -> Lcated a)
     -> m (GenLocated t a)
acsA !l a = do
  !cs <- getCommentsFor (locA l)
  return $ reLoc (a l cs)

ams1 :: MonadP => Located a -> b -> m (LocatedA b)
ams1 (L l a) b = do
  !cs <- getCommentsFor l
  return (L (EpANn (spanAsAnchor l) noAnn cs) b)

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
epUniTokk t@(L !l _) = EpUniTok (EpaSpan l) u
  where
    u = if isUnicode t then UnicodeSyntax else NormalSyntax

-- -------------------------------------

addTrailingVbarA :: MonadP m => LocatedA a -> SrcSpan -> m (LocatedA a)
addTrailingVbarA la span = addTrailingAnnA la span AddVbarAnn

addTrailingSemiA :: MonadP m => LocatedA a -> LocatedA a -> SrcSpan -> m (LocatedA a)
addTrailingSemiA la span = addTrailingAnnA la span AddSemiAnn

addTrailingCommaA :: MonadP m => LocatedA -> SrcSpan -> m (LocatedA a)
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
  in L (EpAnn lr (AnnContext (Just (u, glAA lt)) o c) (cs Semi.<> csc)) 

-- -------------------------------------

combineHasLocs :: (HasLoc a, HasLoc b) => a -> b -> SrcSpan
combineHasLocs a b = combineSrcSpans (getHasLoc a) (getHasLoc b)
}
