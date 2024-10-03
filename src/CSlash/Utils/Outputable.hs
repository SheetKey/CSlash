{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE FlexibleContexts #-}

module CSlash.Utils.Outputable (
  Outputable(..), OutputableBndr(..), OutputableP(..),
  BindingSite(..),  JoinPointHood(..), isJoinPoint,

  IsOutput(..), IsLine(..), IsDoc(..),
  HLine, HDoc,

  SDoc, runSDoc, PDoc(..),
  docToSDoc,
  interppSP, interpp'SP, interpp'SP',
  pprQuotedList, pprWithCommas,
  quotedListWithOr, quotedListWithNor, quotedListWithAnd,
  pprWithBars,
  spaceIfSingleQuote,
  isEmpty, nest,
  ptext,
  int, intWithCommas, integer, word64, word, float, double, rational, doublePrec,
  parens, cparen, brackets, braces, quotes, quote, -- quoteIfPunsEnabled,
  doubleQuotes, angleBrackets,
  semi, comma, colon, dcolon, space, equals, dot, vbar,
  arrow, lollipop, larrow, darrow, arrowt, larrowt, arrowtt, larrowtt,
  lambda,
  lparen, rparen, lbrack, rbrack, lbrace, rbrace, underscore,
  blankLine, forAllLit,
  uKindLit, aKindLit, lKindLit,
  bullet,
  ($+$),
  cat, fcat,
  hang, hangNotEmpty, punctuate, punctuateFinal,
  ppWhen, ppUnless, ppWhenOption, ppUnlessOption,
  speakNth, speakN, speakNOf, plural, singular,
  isOrAre, doOrDoes, itsOrTheir, thisOrThese, hasOrHave,
  itOrThey,
  unicodeSyntax,

  coloured, keyword,

  printSDoc, printSDocLn,
  bufLeftRenderSDoc,
  pprCode,
  showSDocOneLine,
  showSDocUnsafe,
  showPprUnsafe,
  renderWithContext,
  pprDebugAndThen,

  pprInfixVar, pprPrefixVar,
  pprCsChar, pprCsString, 

  primFloatSuffix, primCharSuffix, primDoubleSuffix,
  primInt8Suffix, primWord8Suffix,
  primInt16Suffix, primWord16Suffix,
  primInt32Suffix, primWord32Suffix,
  primInt64Suffix, primWord64Suffix,
  primIntSuffix, primWordSuffix,

  pprPrimChar, pprPrimInt, pprPrimWord,
  pprPrimInt8, pprPrimWord8,
  pprPrimInt16, pprPrimWord16,
  pprPrimInt32, pprPrimWord32,
  pprPrimInt64, pprPrimWord64,

  pprFastFilePath, pprFilePathString,

  pprModuleName,

  PprStyle(..), NamePprCtx(..),
  QueryQualifyName, QueryQualifyModule, QueryQualifyPackage, QueryPromotionTick,
  PromotedItem(..), IsEmptyOrSingleton(..), isListEmptyOrSingleton,
  PromotionTickContext(..),
  reallyAlwaysQualify, reallyAlwaysQualifyNames,
  alwaysQualify, alwaysQualifyNames, alwaysQualifyModules,
  neverQualify, neverQualifyNames, neverQualifyModules,
  alwaysQualifyPackages, neverQualifyPackages,
  alwaysPrintPromTick,
  QualifyName(..), queryQual,
  sdocOption,
  updSDocContext,
  SDocContext (..), sdocWithContext,
  defaultSDocContext, traceSDocContext,
  getPprStyle, withPprStyle, setStyleColoured,
  pprDeeper, pprDeeperList, pprSetDepth,
  codeStyle, userStyle, dumpStyle,
  qualName, qualModule, qualPackage, promTick,
  mkErrStyle, defaultErrStyle, defaultDumpStyle, mkDumpStyle, defaultUserStyle,
  mkUserStyle, cmdlineParserStyle, Depth(..),
  withUserStyle, withErrStyle,

  ifPprDebug, whenPprDebug, getPprDebug,

  bPutHDoc
  ) where

import Prelude hiding ((<>))

import CSlash.Language.Syntax.Module.Name ( ModuleName(..) )

import {-# SOURCE #-} CSlash.Unit.Types ( Unit, Module, moduleName )
import {-# SOURCE #-} CSlash.Types.Name.Occurrence ( OccName )

import CSlash.Utils.BufHandle (BufHandle, bPutChar, bPutStr, bPutFS, bPutFZS)
import CSlash.Data.FastString
import qualified CSlash.Utils.Ppr as Pretty
import qualified CSlash.Utils.Ppr.Color as Col
import CSlash.Utils.Ppr ( Doc, Mode(..) )
import CSlash.Utils.Panic.Plain (assert)
import CSlash.Utils.GlobalVars ( unsafeHasPprDebug )
import CSlash.Utils.Misc (lastMaybe)

import Data.Char
import qualified Data.Map as M
import Data.Int
import Data.Set (Set)
import qualified Data.Set as Set
import Data.String
import Data.Word
import System.IO ( Handle )
import System.FilePath
import Numeric (showFFloat)
import Data.List (intersperse)
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NEL
import Data.Void

import CSlash.Show
import CSlash.Utils.Exception
import GHC.Exts (oneShot)

data PprStyle
  = PprUser NamePprCtx Depth Coloured
  | PprDump NamePprCtx
  | PprCode

data Depth
   = AllTheWay
   | PartWay Int
   | DefaultDepth

data Coloured
  = Uncoloured
  | Coloured

data NamePprCtx = QueryQualify {
    queryQualifyName    :: QueryQualifyName,
    queryQualifyModule  :: QueryQualifyModule,
    queryQualifyPackage :: QueryQualifyPackage,
    queryPromotionTick  :: QueryPromotionTick
}

type QueryQualifyName = Module -> OccName -> QualifyName

type QueryQualifyModule = Module -> Bool

type QueryQualifyPackage = Unit -> Bool

type QueryPromotionTick = PromotedItem -> Bool

data PromotionTickContext =
  PromTickCtx {
    ptcListTuplePuns :: !Bool,
    ptcPrintRedundantPromTicks :: !Bool
  }

data PromotedItem =
    PromotedItemListSyntax IsEmptyOrSingleton
  | PromotedItemTupleSyntax                  
  | PromotedItemDataCon OccName              

newtype IsEmptyOrSingleton = IsEmptyOrSingleton Bool

isListEmptyOrSingleton :: [a] -> IsEmptyOrSingleton
isListEmptyOrSingleton xs =
  IsEmptyOrSingleton $ case xs of
    []  -> True
    [_] -> True
    _   -> False

data QualifyName
  = NameUnqual  
  | NameQual ModuleName
  | NameNotInScope1    
  | NameNotInScope2    

instance Outputable QualifyName where
  ppr NameUnqual      = text "NameUnqual"
  ppr (NameQual _mod) = text "NameQual"
  ppr NameNotInScope1 = text "NameNotInScope1"
  ppr NameNotInScope2 = text "NameNotInScope2"

reallyAlwaysQualifyNames :: QueryQualifyName
reallyAlwaysQualifyNames _ _ = NameNotInScope2

alwaysQualifyNames :: QueryQualifyName
alwaysQualifyNames m _ = NameQual (moduleName m)

neverQualifyNames :: QueryQualifyName
neverQualifyNames _ _ = NameUnqual

alwaysQualifyModules :: QueryQualifyModule
alwaysQualifyModules _ = True

neverQualifyModules :: QueryQualifyModule
neverQualifyModules _ = False

alwaysQualifyPackages :: QueryQualifyPackage
alwaysQualifyPackages _ = True

neverQualifyPackages :: QueryQualifyPackage
neverQualifyPackages _ = False

alwaysPrintPromTick :: QueryPromotionTick
alwaysPrintPromTick _ = True

reallyAlwaysQualify, alwaysQualify, neverQualify :: NamePprCtx
reallyAlwaysQualify
              = QueryQualify reallyAlwaysQualifyNames
                             alwaysQualifyModules
                             alwaysQualifyPackages
                             alwaysPrintPromTick
alwaysQualify = QueryQualify alwaysQualifyNames
                             alwaysQualifyModules
                             alwaysQualifyPackages
                             alwaysPrintPromTick
neverQualify  = QueryQualify neverQualifyNames
                             neverQualifyModules
                             neverQualifyPackages
                             alwaysPrintPromTick

defaultUserStyle :: PprStyle
defaultUserStyle = mkUserStyle neverQualify AllTheWay

defaultDumpStyle :: PprStyle
defaultDumpStyle = PprDump neverQualify

mkDumpStyle :: NamePprCtx -> PprStyle
mkDumpStyle name_ppr_ctx = PprDump name_ppr_ctx

defaultErrStyle :: PprStyle
defaultErrStyle = mkErrStyle neverQualify

mkErrStyle :: NamePprCtx -> PprStyle
mkErrStyle name_ppr_ctx = mkUserStyle name_ppr_ctx DefaultDepth

cmdlineParserStyle :: PprStyle
cmdlineParserStyle = mkUserStyle alwaysQualify AllTheWay

mkUserStyle :: NamePprCtx -> Depth -> PprStyle
mkUserStyle name_ppr_ctx depth = PprUser name_ppr_ctx depth Uncoloured

withUserStyle :: NamePprCtx -> Depth -> SDoc -> SDoc
withUserStyle name_ppr_ctx depth doc =
  withPprStyle (PprUser name_ppr_ctx depth Uncoloured) doc

withErrStyle :: NamePprCtx -> SDoc -> SDoc
withErrStyle name_ppr_ctx doc =
   withPprStyle (mkErrStyle name_ppr_ctx) doc

setStyleColoured :: Bool -> PprStyle -> PprStyle
setStyleColoured col style =
  case style of
    PprUser q d _ -> PprUser q d c
    _             -> style
  where
    c | col       = Coloured
      | otherwise = Uncoloured

instance Outputable PprStyle where
  ppr (PprUser {})  = text "user-style"
  ppr (PprCode {})  = text "code-style"
  ppr (PprDump {})  = text "dump-style"

newtype SDoc = SDoc' (SDocContext -> Doc)

{-# COMPLETE SDoc #-}
pattern SDoc :: (SDocContext -> Doc) -> SDoc
pattern SDoc m <- SDoc' m
  where
    SDoc m = SDoc' (oneShot m)

runSDoc :: SDoc -> (SDocContext -> Doc)
runSDoc (SDoc m) = m

data SDocContext = SDC
  { sdocStyle                       :: !PprStyle
  , sdocColScheme                   :: !Col.Scheme
  , sdocLastColour                  :: !Col.PprColour
  , sdocShouldUseColor              :: !Bool
  , sdocDefaultDepth                :: !Int
  , sdocLineLength                  :: !Int
  , sdocCanUseUnicode               :: !Bool
  , sdocPrintErrIndexLinks          :: !Bool
  , sdocHexWordLiterals             :: !Bool
  , sdocPprDebug                    :: !Bool
  , sdocPrintUnicodeSyntax          :: !Bool
  , sdocPrintCaseAsLet              :: !Bool
  , sdocPrintTypecheckerElaboration :: !Bool
  , sdocSuppressTicks               :: !Bool
  , sdocSuppressTypeSignatures      :: !Bool
  , sdocSuppressIdInfo              :: !Bool
  , sdocSuppressUnfoldings          :: !Bool
  , sdocSuppressUniques             :: !Bool
  , sdocSuppressModulePrefixes      :: !Bool
  , sdocErrorSpans                  :: !Bool
  , sdocPrintTypeAbbreviations      :: !Bool
  , sdocUnitIdForUser               :: !(FastString -> SDoc)
  }

instance IsString SDoc where
  fromString = text

instance Outputable SDoc where
  ppr = id

defaultSDocContext :: SDocContext
defaultSDocContext = SDC
  { sdocStyle                       = defaultDumpStyle
  , sdocColScheme                   = Col.defaultScheme
  , sdocLastColour                  = Col.colReset
  , sdocShouldUseColor              = False
  , sdocDefaultDepth                = 5
  , sdocLineLength                  = 100
  , sdocCanUseUnicode               = False
  , sdocPrintErrIndexLinks          = False
  , sdocHexWordLiterals             = False
  , sdocPprDebug                    = False
  , sdocPrintUnicodeSyntax          = False
  , sdocPrintCaseAsLet              = False
  , sdocPrintTypecheckerElaboration = False
  , sdocSuppressTicks               = False
  , sdocSuppressTypeSignatures      = False
  , sdocSuppressIdInfo              = False
  , sdocSuppressUnfoldings          = False
  , sdocSuppressUniques             = False
  , sdocSuppressModulePrefixes      = False
  , sdocErrorSpans                  = False
  -- , sdocStarIsType                  = False
  -- , sdocLinearTypes                 = False
  -- , sdocListTuplePuns               = True
  , sdocPrintTypeAbbreviations      = True
  , sdocUnitIdForUser               = ftext
  }

traceSDocContext :: SDocContext
traceSDocContext = defaultSDocContext
  { sdocPprDebug                    = unsafeHasPprDebug
  , sdocPrintTypecheckerElaboration = True
  }

withPprStyle :: PprStyle -> SDoc -> SDoc
{-# INLINE CONLIKE withPprStyle #-}
withPprStyle sty d = SDoc $ \ctxt -> runSDoc d ctxt{sdocStyle=sty}

pprDeeper :: SDoc -> SDoc
pprDeeper d = SDoc $ \ctx -> case sdocStyle ctx of
  PprUser q depth c ->
   let deeper 0 = Pretty.text "..."
       deeper n = runSDoc d ctx{sdocStyle = PprUser q (PartWay (n-1)) c}
   in case depth of
         DefaultDepth -> deeper (sdocDefaultDepth ctx)
         PartWay n    -> deeper n
         AllTheWay    -> runSDoc d ctx
  _ -> runSDoc d ctx

pprDeeperList :: ([SDoc] -> SDoc) -> [SDoc] -> SDoc
pprDeeperList f ds
  | null ds   = f []
  | otherwise = SDoc work
 where
  work ctx@SDC{sdocStyle=PprUser q depth c}
   | DefaultDepth <- depth
   = work (ctx { sdocStyle = PprUser q (PartWay (sdocDefaultDepth ctx)) c })
   | PartWay 0 <- depth
   = Pretty.text "..."
   | PartWay n <- depth
   = let
        go _ [] = []
        go i (d:ds) | i >= n    = [text "...."]
                    | otherwise = d : go (i+1) ds
     in runSDoc (f (go 0 ds)) ctx{sdocStyle = PprUser q (PartWay (n-1)) c}
  work other_ctx = runSDoc (f ds) other_ctx

pprSetDepth :: Depth -> SDoc -> SDoc
pprSetDepth depth doc = SDoc $ \ctx ->
    case ctx of
        SDC{sdocStyle=PprUser q _ c} ->
            runSDoc doc ctx{sdocStyle = PprUser q depth c}
        _ ->
            runSDoc doc ctx

getPprStyle :: (PprStyle -> SDoc) -> SDoc
{-# INLINE CONLIKE getPprStyle #-}
getPprStyle df = SDoc $ \ctx -> runSDoc (df (sdocStyle ctx)) ctx

sdocWithContext :: (SDocContext -> SDoc) -> SDoc
{-# INLINE CONLIKE sdocWithContext #-}
sdocWithContext f = SDoc $ \ctx -> runSDoc (f ctx) ctx

sdocOption :: (SDocContext -> a) -> (a -> SDoc) -> SDoc
{-# INLINE CONLIKE sdocOption #-}
sdocOption f g = sdocWithContext (g . f)

updSDocContext :: (SDocContext -> SDocContext) -> SDoc -> SDoc
{-# INLINE CONLIKE updSDocContext #-}
updSDocContext upd doc
  = SDoc $ \ctx -> runSDoc doc (upd ctx)

qualName :: PprStyle -> QueryQualifyName
qualName (PprUser q _ _) mod occ = queryQualifyName q mod occ
qualName (PprDump q)     mod occ = queryQualifyName q mod occ
qualName _other          mod _   = NameQual (moduleName mod)

qualModule :: PprStyle -> QueryQualifyModule
qualModule (PprUser q _ _)  m = queryQualifyModule q m
qualModule (PprDump q)      m = queryQualifyModule q m
qualModule _other          _m = True

qualPackage :: PprStyle -> QueryQualifyPackage
qualPackage (PprUser q _ _)  m = queryQualifyPackage q m
qualPackage (PprDump q)      m = queryQualifyPackage q m
qualPackage _other          _m = True

promTick :: PprStyle -> QueryPromotionTick
promTick (PprUser q _ _) occ = queryPromotionTick q occ
promTick (PprDump q)     occ = queryPromotionTick q occ
promTick _               _   = True

queryQual :: PprStyle -> NamePprCtx
queryQual s = QueryQualify (qualName s)
                           (qualModule s)
                           (qualPackage s)
                           (promTick s)

codeStyle :: PprStyle -> Bool
codeStyle PprCode     = True
codeStyle _           = False

dumpStyle :: PprStyle -> Bool
dumpStyle (PprDump {}) = True
dumpStyle _other       = False

userStyle ::  PprStyle -> Bool
userStyle (PprUser {}) = True
userStyle _other       = False

getPprDebug :: IsOutput doc => (Bool -> doc) -> doc
{-# INLINE CONLIKE getPprDebug #-}
getPprDebug d = docWithContext $ \ctx -> d (sdocPprDebug ctx)

ifPprDebug :: IsOutput doc => doc -> doc -> doc
{-# INLINE CONLIKE ifPprDebug #-}
ifPprDebug yes no = getPprDebug $ \dbg -> if dbg then yes else no

whenPprDebug :: IsOutput doc => doc -> doc
{-# INLINE CONLIKE whenPprDebug #-}
whenPprDebug d = ifPprDebug d empty

printSDoc :: SDocContext -> Mode -> Handle -> SDoc -> IO ()
printSDoc ctx mode handle doc =
  Pretty.printDoc_ mode cols handle (runSDoc doc ctx)
    `finally`
      Pretty.printDoc_ mode cols handle
        (runSDoc (coloured Col.colReset empty) ctx)
  where
    cols = sdocLineLength ctx

printSDocLn :: SDocContext -> Mode -> Handle -> SDoc -> IO ()
printSDocLn ctx mode handle doc =
  printSDoc ctx mode handle (doc $$ text "")

bufLeftRenderSDoc :: SDocContext -> BufHandle -> SDoc -> IO ()
bufLeftRenderSDoc ctx bufHandle doc =
  Pretty.bufLeftRender bufHandle (runSDoc doc ctx)

pprCode :: SDoc -> SDoc
{-# INLINE CONLIKE pprCode #-}
pprCode d = withPprStyle PprCode d

renderWithContext :: SDocContext -> SDoc -> String
renderWithContext ctx sdoc
  = let s = Pretty.style{ Pretty.mode       = PageMode False,
                          Pretty.lineLength = sdocLineLength ctx }
    in Pretty.renderStyle s $ runSDoc sdoc ctx

showSDocOneLine :: SDocContext -> SDoc -> String
showSDocOneLine ctx d
 = let s = Pretty.style{ Pretty.mode = OneLineMode,
                         Pretty.lineLength = sdocLineLength ctx } in
   Pretty.renderStyle s $
      runSDoc d ctx

showSDocUnsafe :: SDoc -> String
showSDocUnsafe sdoc = renderWithContext defaultSDocContext sdoc

showPprUnsafe :: Outputable a => a -> String
showPprUnsafe a = renderWithContext defaultSDocContext (ppr a)

pprDebugAndThen :: SDocContext -> (String -> a) -> SDoc -> SDoc -> a
pprDebugAndThen ctx cont heading pretty_msg
 = cont (renderWithContext ctx doc)
 where
     doc = withPprStyle defaultDumpStyle (sep [heading, nest 2 pretty_msg])

isEmpty :: SDocContext -> SDoc -> Bool
isEmpty ctx sdoc = Pretty.isEmpty $ runSDoc sdoc (ctx {sdocPprDebug = True})

docToSDoc :: Doc -> SDoc
docToSDoc d = SDoc (\_ -> d)

ptext    ::               PtrString  -> SDoc
int      :: IsLine doc => Int        -> doc
integer  :: IsLine doc => Integer    -> doc
word     ::               Integer    -> SDoc
word64   :: IsLine doc => Word64     -> doc
float    :: IsLine doc => Float      -> doc
double   :: IsLine doc => Double     -> doc
rational ::               Rational   -> SDoc

{-# INLINE CONLIKE ptext #-}
ptext s     = docToSDoc $ Pretty.ptext s
{-# INLINE CONLIKE int #-}
int n       = text $ show n
{-# INLINE CONLIKE integer #-}
integer n   = text $ show n
{-# INLINE CONLIKE float #-}
float n     = text $ show n
{-# INLINE CONLIKE double #-}
double n    = text $ show n
{-# INLINE CONLIKE rational #-}
rational n  = text $ show n
{-# INLINE CONLIKE word64 #-}
word64 n    = text $ show n
{-# INLINE CONLIKE word #-}
word n      = sdocOption sdocHexWordLiterals $ \case
               True  -> docToSDoc $ Pretty.hex n
               False -> docToSDoc $ Pretty.integer n

doublePrec :: Int -> Double -> SDoc
doublePrec p n = text (showFFloat (Just p) n "")

quotes, quote :: SDoc -> SDoc
parens, brackets, braces, doubleQuotes, angleBrackets :: IsLine doc => doc -> doc

{-# INLINE CONLIKE parens #-}
parens d        = char '(' <> d <> char ')'
{-# INLINE CONLIKE braces #-}
braces d        = char '{' <> d <> char '}'
{-# INLINE CONLIKE brackets #-}
brackets d      = char '[' <> d <> char ']'
{-# INLINE CONLIKE quote #-}
quote d         = SDoc $ Pretty.quote . runSDoc d
{-# INLINE CONLIKE doubleQuotes #-}
doubleQuotes d  = char '"' <> d <> char '"'
{-# INLINE CONLIKE angleBrackets #-}
angleBrackets d = char '<' <> d <> char '>'

cparen :: Bool -> SDoc -> SDoc
{-# INLINE CONLIKE cparen #-}
cparen b d = SDoc $ Pretty.maybeParens b . runSDoc d

-- quoteIfPunsEnabled :: SDoc -> SDoc
-- quoteIfPunsEnabled doc =
--   sdocOption sdocListTuplePuns $ \case
--     True -> quote doc
--     False -> doc

quotes d = sdocOption sdocCanUseUnicode $ \case
   True  -> char '‘' <> d <> char '’'
   False -> SDoc $ \sty ->
      let pp_d = runSDoc d sty
          str  = show pp_d
      in case str of
         []                   -> Pretty.quotes pp_d
         '\'' : _             -> pp_d
         _ | Just '\'' <- lastMaybe str -> pp_d
           | otherwise        -> Pretty.quotes pp_d

blankLine, dcolon, arrow, lollipop, larrow, darrow, arrowt, larrowt, arrowtt,
  larrowtt, lambda :: SDoc

blankLine  = docToSDoc Pretty.emptyText
dcolon     = unicodeSyntax (char '∷') (text "::")
arrow      = unicodeSyntax (char '→') (text "->")
lollipop   = unicodeSyntax (char '⊸') (text "%1 ->")
larrow     = unicodeSyntax (char '←') (text "<-")
darrow     = unicodeSyntax (char '⇒') (text "=>")
arrowt     = unicodeSyntax (char '⤚') (text ">-")
larrowt    = unicodeSyntax (char '⤙') (text "-<")
arrowtt    = unicodeSyntax (char '⤜') (text ">>-")
larrowtt   = unicodeSyntax (char '⤛') (text "-<<")
lambda     = unicodeSyntax (char 'λ') (char '\\')

semi, comma, colon, equals, space, underscore, dot, vbar :: IsLine doc => doc
lparen, rparen, lbrack, rbrack, lbrace, rbrace :: IsLine doc => doc
semi       = char ';'
comma      = char ','
colon      = char ':'
equals     = char '='
space      = char ' '
underscore = char '_'
dot        = char '.'
vbar       = char '|'
lparen     = char '('
rparen     = char ')'
lbrack     = char '['
rbrack     = char ']'
lbrace     = char '{'
rbrace     = char '}'

forAllLit :: SDoc
forAllLit = unicodeSyntax (char '∀') (text "forall")

uKindLit :: SDoc
uKindLit = unicodeSyntax (char '★') (text "UK")

aKindLit :: SDoc
aKindLit = unicodeSyntax (char '○') (text "AK")

lKindLit :: SDoc
lKindLit = unicodeSyntax (char '●') (text "LK")

bullet :: SDoc
bullet = unicode (char '•') (char '*')

unicodeSyntax :: SDoc -> SDoc -> SDoc
unicodeSyntax unicode plain =
   sdocOption sdocCanUseUnicode $ \can_use_unicode ->
   sdocOption sdocPrintUnicodeSyntax $ \print_unicode_syntax ->
    if can_use_unicode && print_unicode_syntax
    then unicode
    else plain

unicode :: SDoc -> SDoc -> SDoc
unicode unicode plain = sdocOption sdocCanUseUnicode $ \case
   True  -> unicode
   False -> plain

nest :: Int -> SDoc -> SDoc
($+$) :: SDoc -> SDoc -> SDoc

{-# INLINE CONLIKE nest #-}
nest n d    = SDoc $ Pretty.nest n . runSDoc d
{-# INLINE CONLIKE ($+$) #-}
($+$) d1 d2 = SDoc $ \ctx -> (Pretty.$+$) (runSDoc d1 ctx) (runSDoc d2 ctx)

cat :: [SDoc] -> SDoc
fcat :: [SDoc] -> SDoc

{-# INLINE CONLIKE cat #-}
cat ds  = SDoc $ \ctx -> Pretty.cat  [runSDoc d ctx | d <- ds]
{-# INLINE CONLIKE fcat #-}
fcat ds = SDoc $ \ctx -> Pretty.fcat [runSDoc d ctx | d <- ds]

hang :: SDoc
      -> Int
      -> SDoc
      -> SDoc
{-# INLINE CONLIKE hang #-}
hang d1 n d2   = SDoc $ \sty -> Pretty.hang (runSDoc d1 sty) n (runSDoc d2 sty)

hangNotEmpty :: SDoc -> Int -> SDoc -> SDoc
{-# INLINE CONLIKE hangNotEmpty #-}
hangNotEmpty d1 n d2 =
    SDoc $ \ctx -> Pretty.hangNotEmpty (runSDoc d1 ctx) n (runSDoc d2 ctx)

punctuate :: IsLine doc
          => doc
          -> [doc]
          -> [doc]
punctuate _ []     = []
punctuate p (d:ds) = go d ds
                   where
                     go d [] = [d]
                     go d (e:es) = (d <> p) : go e es

punctuateFinal :: IsLine doc
               => doc
               -> doc
               -> [doc]
               -> [doc]
punctuateFinal _ _ []     = []
punctuateFinal p q (d:ds) = go d ds
  where
    go d [] = [d <> q]
    go d (e:es) = (d <> p) : go e es

ppWhen, ppUnless :: IsOutput doc => Bool -> doc -> doc
{-# INLINE CONLIKE ppWhen #-}
ppWhen True  doc = doc
ppWhen False _   = empty

{-# INLINE CONLIKE ppUnless #-}
ppUnless True  _   = empty
ppUnless False doc = doc

{-# INLINE CONLIKE ppWhenOption #-}
ppWhenOption :: (SDocContext -> Bool) -> SDoc -> SDoc
ppWhenOption f doc = sdocOption f $ \case
   True  -> doc
   False -> empty

{-# INLINE CONLIKE ppUnlessOption #-}
ppUnlessOption :: (SDocContext -> Bool) -> SDoc -> SDoc
ppUnlessOption f doc = sdocOption f $ \case
   True  -> empty
   False -> doc

coloured :: Col.PprColour -> SDoc -> SDoc
coloured col sdoc = sdocOption sdocShouldUseColor $ \case
   True -> SDoc $ \case
      ctx@SDC{ sdocLastColour = lastCol, sdocStyle = PprUser _ _ Coloured } ->
         let ctx' = ctx{ sdocLastColour = lastCol `mappend` col } in
         Pretty.zeroWidthText (Col.renderColour col)
           Pretty.<> runSDoc sdoc ctx'
           Pretty.<> Pretty.zeroWidthText (Col.renderColourAfresh lastCol)
      ctx -> runSDoc sdoc ctx
   False -> sdoc

keyword :: SDoc -> SDoc
keyword = coloured Col.colBold

class Outputable a where
    ppr :: a -> SDoc

instance Outputable Void where
    ppr _ = text "<<Void>>"

instance Outputable Bool where
    ppr True  = text "True"
    ppr False = text "False"

instance Outputable Ordering where
    ppr LT = text "LT"
    ppr EQ = text "EQ"
    ppr GT = text "GT"

instance Outputable Int8 where
   ppr n = integer $ fromIntegral n

instance Outputable Int16 where
   ppr n = integer $ fromIntegral n

instance Outputable Int32 where
   ppr n = integer $ fromIntegral n

instance Outputable Int64 where
   ppr n = integer $ fromIntegral n

instance Outputable Int where
    ppr n = int n

instance Outputable Integer where
    ppr n = integer n

instance Outputable Word8 where
    ppr n = integer $ fromIntegral n

instance Outputable Word16 where
    ppr n = integer $ fromIntegral n

instance Outputable Word32 where
    ppr n = integer $ fromIntegral n

instance Outputable Word64 where
    ppr n = integer $ fromIntegral n

instance Outputable Word where
    ppr n = integer $ fromIntegral n

instance Outputable Float where
    ppr f = float f

instance Outputable Double where
    ppr f = double f

instance Outputable () where
    ppr _ = text "()"

instance (Outputable a) => Outputable [a] where
    ppr xs = brackets (pprWithCommas ppr xs)

instance (Outputable a) => Outputable (NonEmpty a) where
    ppr = ppr . NEL.toList

instance (Outputable a) => Outputable (Set a) where
  ppr s = braces (pprWithCommas ppr (Set.toList s))

instance (Outputable a, Outputable b) => Outputable (a, b) where
    ppr (x,y) = parens (sep [ppr x <> comma, ppr y])

instance Outputable a => Outputable (Maybe a) where
    ppr Nothing  = text "Nothing"
    ppr (Just x) = text "Just" <+> ppr x

instance (Outputable a, Outputable b) => Outputable (Either a b) where
    ppr (Left x)  = text "Left"  <+> ppr x
    ppr (Right y) = text "Right" <+> ppr y

instance (Outputable a, Outputable b, Outputable c) => Outputable (a, b, c) where
    ppr (x,y,z) =
      parens (sep [ppr x <> comma,
                   ppr y <> comma,
                   ppr z ])

instance (Outputable a, Outputable b, Outputable c, Outputable d) =>
         Outputable (a, b, c, d) where
    ppr (a,b,c,d) =
      parens (sep [ppr a <> comma,
                   ppr b <> comma,
                   ppr c <> comma,
                   ppr d])

instance (Outputable a, Outputable b, Outputable c, Outputable d, Outputable e) =>
         Outputable (a, b, c, d, e) where
    ppr (a,b,c,d,e) =
      parens (sep [ppr a <> comma,
                   ppr b <> comma,
                   ppr c <> comma,
                   ppr d <> comma,
                   ppr e])

instance (Outputable a, Outputable b, Outputable c, Outputable d, Outputable e, Outputable f) =>
         Outputable (a, b, c, d, e, f) where
    ppr (a,b,c,d,e,f) =
      parens (sep [ppr a <> comma,
                   ppr b <> comma,
                   ppr c <> comma,
                   ppr d <> comma,
                   ppr e <> comma,
                   ppr f])

instance (Outputable a, Outputable b, Outputable c, Outputable d, Outputable e, Outputable f, Outputable g) =>
         Outputable (a, b, c, d, e, f, g) where
    ppr (a,b,c,d,e,f,g) =
      parens (sep [ppr a <> comma,
                   ppr b <> comma,
                   ppr c <> comma,
                   ppr d <> comma,
                   ppr e <> comma,
                   ppr f <> comma,
                   ppr g])

instance Outputable FastString where
    ppr fs = ftext fs       

deriving newtype instance Outputable NonDetFastString
deriving newtype instance Outputable LexicalFastString

instance (Outputable key, Outputable elt) => Outputable (M.Map key elt) where
  ppr m = ppr (M.toList m)

instance Outputable ModuleName where
  ppr = pprModuleName

pprModuleName :: IsLine doc => ModuleName -> doc
pprModuleName (ModuleName nm) =
    docWithStyle (ztext (zEncodeFS nm)) (\_ -> ftext nm)
{-# SPECIALIZE pprModuleName :: ModuleName -> SDoc #-}
{-# SPECIALIZE pprModuleName :: ModuleName -> HLine #-} 

class OutputableP env a where
   pdoc :: env -> a -> SDoc

newtype PDoc a = PDoc a

instance Outputable a => OutputableP env (PDoc a) where
   pdoc _ (PDoc a) = ppr a

instance OutputableP env a => OutputableP env [a] where
   pdoc env xs = ppr (fmap (pdoc env) xs)

instance OutputableP env a => OutputableP env (Maybe a) where
   pdoc env xs = ppr (fmap (pdoc env) xs)

instance (OutputableP env a, OutputableP env b) => OutputableP env (a, b) where
    pdoc env (a,b) = ppr (pdoc env a, pdoc env b)

instance (OutputableP env a, OutputableP env b, OutputableP env c) => OutputableP env (a, b, c) where
    pdoc env (a,b,c) = ppr (pdoc env a, pdoc env b, pdoc env c)

instance OutputableP env SDoc where
   pdoc _ x = x

instance OutputableP env Void where
    pdoc _ = \ case

class Outputable a => OutputableBndr a where
   pprBndr :: BindingSite -> a -> SDoc
   pprBndr _b x = ppr x

   pprPrefixOcc, pprInfixOcc :: a -> SDoc

   bndrIsJoin_maybe :: a -> JoinPointHood
   bndrIsJoin_maybe _ = NotJoinPoint

data BindingSite
    = LambdaBind
    | CaseBind  
    | CasePatBind
    | LetBind    
    deriving Eq

data JoinPointHood
  = JoinPoint {-# UNPACK #-} !Int
  | NotJoinPoint                 
  deriving( Eq )

isJoinPoint :: JoinPointHood -> Bool
isJoinPoint (JoinPoint {}) = True
isJoinPoint NotJoinPoint   = False

instance Outputable JoinPointHood where
  ppr NotJoinPoint      = text "NotJoinPoint"
  ppr (JoinPoint arity) = text "JoinPoint" <> parens (ppr arity)

pprCsChar :: Char -> SDoc
pprCsChar c | c > '\x10ffff' = char '\\' <> text (show (fromIntegral (ord c) :: Word32))
            | otherwise      = text (show c)

pprCsString :: FastString -> SDoc
pprCsString fs = vcat (map text (showMultiLineString (unpackFS fs)))

primCharSuffix, primFloatSuffix, primDoubleSuffix,
  primIntSuffix, primWordSuffix,
  primInt8Suffix, primWord8Suffix,
  primInt16Suffix, primWord16Suffix,
  primInt32Suffix, primWord32Suffix,
  primInt64Suffix, primWord64Suffix
  :: SDoc
primCharSuffix   = char '#'
primFloatSuffix  = char '#'
primIntSuffix    = char '#'
primDoubleSuffix = text "##"
primWordSuffix   = text "##"
primInt8Suffix   = text "#Int8"
primWord8Suffix  = text "#Word8"
primInt16Suffix  = text "#Int16"
primWord16Suffix = text "#Word16"
primInt32Suffix  = text "#Int32"
primWord32Suffix = text "#Word32"
primInt64Suffix  = text "#Int64"
primWord64Suffix = text "#Word64"

pprPrimChar :: Char -> SDoc
pprPrimInt, pprPrimWord,
  pprPrimInt8, pprPrimWord8,
  pprPrimInt16, pprPrimWord16,
  pprPrimInt32, pprPrimWord32,
  pprPrimInt64, pprPrimWord64
  :: Integer -> SDoc
pprPrimChar c   = pprCsChar c <> primCharSuffix
pprPrimInt i    = integer i   <> primIntSuffix
pprPrimWord w   = word    w   <> primWordSuffix
pprPrimInt8 i   = integer i   <> primInt8Suffix
pprPrimInt16 i  = integer i   <> primInt16Suffix
pprPrimInt32 i  = integer i   <> primInt32Suffix
pprPrimInt64 i  = integer i   <> primInt64Suffix
pprPrimWord8 w  = word    w   <> primWord8Suffix
pprPrimWord16 w = word    w   <> primWord16Suffix
pprPrimWord32 w = word    w   <> primWord32Suffix
pprPrimWord64 w = word    w   <> primWord64Suffix

pprPrefixVar :: Bool -> SDoc -> SDoc
pprPrefixVar is_operator pp_v
  | is_operator = parens pp_v
  | otherwise   = pp_v

pprInfixVar :: Bool -> SDoc -> SDoc
pprInfixVar is_operator pp_v
  | is_operator = pp_v
  | otherwise   = char '`' <> pp_v <> char '`'

pprFastFilePath :: FastString -> SDoc
pprFastFilePath path = text $ normalise $ unpackFS path

pprFilePathString :: IsLine doc => FilePath -> doc
pprFilePathString path = doubleQuotes $ text (escape (normalise path))
   where
      escape []        = []
      escape ('\\':xs) = '\\':'\\':escape xs
      escape (x:xs)    = x:escape xs
{-# SPECIALIZE pprFilePathString :: FilePath -> SDoc #-}
{-# SPECIALIZE pprFilePathString :: FilePath -> HLine #-}

pprWithCommas :: (a -> SDoc)
              -> [a]        
              -> SDoc       
pprWithCommas pp xs = fsep (punctuate comma (map pp xs))

pprWithBars :: (a -> SDoc)
            -> [a]        
            -> SDoc       
pprWithBars pp xs = fsep (intersperse vbar (map pp xs))

spaceIfSingleQuote :: SDoc -> SDoc
spaceIfSingleQuote (SDoc m) =
  SDoc $ \ctx ->
    let (mHead, d) = Pretty.docHead (m ctx)
    in if mHead == Just '\''
       then Pretty.space Pretty.<> d
       else d

interppSP  :: Outputable a => [a] -> SDoc
interppSP  xs = sep (map ppr xs)

interpp'SP :: Outputable a => [a] -> SDoc
interpp'SP xs = interpp'SP' ppr xs

interpp'SP' :: (a -> SDoc) -> [a] -> SDoc
interpp'SP' f xs = sep (punctuate comma (map f xs))

pprQuotedList :: Outputable a => [a] -> SDoc
pprQuotedList = quotedList . map ppr

quotedList :: [SDoc] -> SDoc
quotedList xs = fsep (punctuate comma (map quotes xs))

quotedListWithOr :: [SDoc] -> SDoc
quotedListWithOr xs@(_:_:_) = quotedList (init xs) <+> text "or" <+> quotes (last xs)
quotedListWithOr xs = quotedList xs

quotedListWithNor :: [SDoc] -> SDoc
quotedListWithNor xs@(_:_:_) = quotedList (init xs) <+> text "nor" <+> quotes (last xs)
quotedListWithNor xs = quotedList xs

quotedListWithAnd :: [SDoc] -> SDoc
quotedListWithAnd xs@(_:_:_) = quotedList (init xs) <+> text "and" <+> quotes (last xs)
quotedListWithAnd xs = quotedList xs

intWithCommas :: Integral a => a -> SDoc
intWithCommas n
  | n < 0     = char '-' <> intWithCommas (-n)
  | q == 0    = int (fromIntegral r)
  | otherwise = intWithCommas q <> comma <> zeroes <> int (fromIntegral r)
  where
    (q,r) = n `quotRem` 1000
    zeroes | r >= 100  = empty
           | r >= 10   = char '0'
           | otherwise = text "00"

speakNth :: Int -> SDoc
speakNth 1 = text "first"
speakNth 2 = text "second"
speakNth 3 = text "third"
speakNth 4 = text "fourth"
speakNth 5 = text "fifth"
speakNth 6 = text "sixth"
speakNth n = hcat [ int n, text suffix ]
  where
    suffix | n <= 20       = "th"
           | last_dig == 1 = "st"
           | last_dig == 2 = "nd"
           | last_dig == 3 = "rd"
           | otherwise     = "th"

    last_dig = n `rem` 10

speakN :: Int -> SDoc
speakN 0 = text "none"  
speakN 1 = text "one"   
speakN 2 = text "two"
speakN 3 = text "three"
speakN 4 = text "four"
speakN 5 = text "five"
speakN 6 = text "six"
speakN n = int n

speakNOf :: Int -> SDoc -> SDoc
speakNOf 0 d = text "no" <+> d <> char 's'
speakNOf 1 d = text "one" <+> d                 
speakNOf n d = speakN n <+> d <> char 's'       

plural :: [a] -> SDoc
plural [_] = empty
plural _   = char 's'

singular :: [a] -> SDoc
singular [_] = char 's'
singular _   = empty

isOrAre :: [a] -> SDoc
isOrAre [_] = text "is"
isOrAre _   = text "are"

doOrDoes :: [a] -> SDoc
doOrDoes [_] = text "does"
doOrDoes _   = text "do"

itsOrTheir :: [a] -> SDoc
itsOrTheir [_] = text "its"
itsOrTheir _   = text "their"

itOrThey :: [a] -> SDoc
itOrThey [_] = text "it"
itOrThey _   = text "they"


thisOrThese :: [a] -> SDoc
thisOrThese [_] = text "This"
thisOrThese _   = text "These"

hasOrHave :: [a] -> SDoc
hasOrHave [_] = text "has"
hasOrHave _   = text "have"

newtype HLine = HLine' { runHLine :: SDocContext -> BufHandle -> IO () }

newtype HDoc = HDoc' { runHDoc :: SDocContext -> BufHandle -> IO () }

pattern HLine :: (SDocContext -> BufHandle -> IO ()) -> HLine
pattern HLine f <- HLine' f
  where HLine f = HLine' (oneShot (\ctx -> oneShot (\h -> f ctx h)))
{-# COMPLETE HLine #-}

pattern HDoc :: (SDocContext -> BufHandle -> IO ()) -> HDoc
pattern HDoc f <- HDoc' f
  where HDoc f = HDoc' (oneShot (\ctx -> oneShot (\h -> f ctx h)))
{-# COMPLETE HDoc #-}

bPutHDoc :: BufHandle -> SDocContext -> HDoc -> IO ()
bPutHDoc h ctx (HDoc f) = assert (codeStyle (sdocStyle ctx)) (f ctx h)

class IsOutput doc where
  empty :: doc
  docWithContext :: (SDocContext -> doc) -> doc
  docWithStyle :: doc -> (PprStyle -> SDoc) -> doc  

class IsOutput doc => IsLine doc where
  char :: Char -> doc
  text :: String -> doc
  ftext :: FastString -> doc
  ztext :: FastZString -> doc

  (<>) :: doc -> doc -> doc
  (<+>) :: doc -> doc -> doc
  sep :: [doc] -> doc
  fsep :: [doc] -> doc

  hcat :: [doc] -> doc
  hcat docs = foldr (<>) empty docs
  {-# INLINE CONLIKE hcat #-}

  hsep :: [doc] -> doc
  hsep docs = foldr (<+>) empty docs
  {-# INLINE CONLIKE hsep #-}

  dualLine :: SDoc -> HLine -> doc

class (IsOutput doc, IsLine (Line doc)) => IsDoc doc where
  type Line doc = r | r -> doc
  line :: Line doc -> doc

  ($$) :: doc -> doc -> doc

  lines_ :: [Line doc] -> doc
  lines_ = vcat . map line
  {-# INLINE CONLIKE lines_ #-}

  vcat :: [doc] -> doc
  vcat ls = foldr ($$) empty ls
  {-# INLINE CONLIKE vcat #-}

  dualDoc :: SDoc -> HDoc -> doc

instance IsOutput SDoc where
  empty       = docToSDoc $ Pretty.empty
  {-# INLINE CONLIKE empty #-}
  docWithContext = sdocWithContext
  {-# INLINE docWithContext #-}
  docWithStyle c f = sdocWithContext (\ctx -> let sty = sdocStyle ctx
                                              in if codeStyle sty then c
                                                                  else f sty)
  {-# INLINE CONLIKE docWithStyle #-}

instance IsLine SDoc where
  char c = docToSDoc $ Pretty.char c
  {-# INLINE CONLIKE char #-}
  text s = docToSDoc $ Pretty.text s
  {-# INLINE CONLIKE text #-}
  ftext s = docToSDoc $ Pretty.ftext s
  {-# INLINE CONLIKE ftext #-}
  ztext s = docToSDoc $ Pretty.ztext s
  {-# INLINE CONLIKE ztext #-}
  (<>) d1 d2 = SDoc $ \ctx -> (Pretty.<>)  (runSDoc d1 ctx) (runSDoc d2 ctx)
  {-# INLINE CONLIKE (<>) #-}
  (<+>) d1 d2 = SDoc $ \ctx -> (Pretty.<+>) (runSDoc d1 ctx) (runSDoc d2 ctx)
  {-# INLINE CONLIKE (<+>) #-}
  hcat ds = SDoc $ \ctx -> Pretty.hcat [runSDoc d ctx | d <- ds]
  {-# INLINE CONLIKE hcat #-}
  hsep ds = SDoc $ \ctx -> Pretty.hsep [runSDoc d ctx | d <- ds]
  {-# INLINE CONLIKE hsep #-}
  sep ds  = SDoc $ \ctx -> Pretty.sep  [runSDoc d ctx | d <- ds]
  {-# INLINE CONLIKE sep #-}
  fsep ds = SDoc $ \ctx -> Pretty.fsep [runSDoc d ctx | d <- ds]
  {-# INLINE CONLIKE fsep #-}
  dualLine s _ = s
  {-# INLINE CONLIKE dualLine #-}

instance IsDoc SDoc where
  type Line SDoc = SDoc
  line = id
  {-# INLINE line #-}
  lines_ = vcat
  {-# INLINE lines_ #-}

  ($$) d1 d2  = SDoc $ \ctx -> (Pretty.$$)  (runSDoc d1 ctx) (runSDoc d2 ctx)
  {-# INLINE CONLIKE ($$) #-}
  vcat ds = SDoc $ \ctx -> Pretty.vcat [runSDoc d ctx | d <- ds]
  {-# INLINE CONLIKE vcat #-}
  dualDoc s _ = s
  {-# INLINE CONLIKE dualDoc #-}

instance IsOutput HLine where
  empty = HLine (\_ _ -> pure ())
  {-# INLINE empty #-}
  docWithContext f = HLine $ \ctx h -> runHLine (f ctx) ctx h
  {-# INLINE CONLIKE docWithContext #-}
  docWithStyle c _ = c  
  {-# INLINE CONLIKE docWithStyle #-}

instance IsOutput HDoc where
  empty = HDoc (\_ _ -> pure ())
  {-# INLINE empty #-}
  docWithContext f = HDoc $ \ctx h -> runHDoc (f ctx) ctx h
  {-# INLINE CONLIKE docWithContext #-}
  docWithStyle c _ = c  
  {-# INLINE CONLIKE docWithStyle #-}

instance IsLine HLine where
  char c = HLine (\_ h -> bPutChar h c)
  {-# INLINE CONLIKE char #-}
  text str = HLine (\_ h -> bPutStr h str)
  {-# INLINE CONLIKE text #-}
  ftext fstr = HLine (\_ h -> bPutFS h fstr)
  {-# INLINE CONLIKE ftext #-}
  ztext fstr = HLine (\_ h -> bPutFZS h fstr)
  {-# INLINE CONLIKE ztext #-}

  HLine f <> HLine g = HLine (\ctx h -> f ctx h *> g ctx h)
  {-# INLINE CONLIKE (<>) #-}
  f <+> g = f <> char ' ' <> g
  {-# INLINE CONLIKE (<+>) #-}
  sep = hsep
  {-# INLINE sep #-}
  fsep = hsep
  {-# INLINE fsep #-}

  dualLine _ h = h
  {-# INLINE CONLIKE dualLine #-}

instance IsDoc HDoc where
  type Line HDoc = HLine
  line (HLine f) = HDoc (\ctx h -> f ctx h *> bPutChar h '\n')
  {-# INLINE CONLIKE line #-}
  HDoc f $$ HDoc g = HDoc (\ctx h -> f ctx h *> g ctx h)
  {-# INLINE CONLIKE ($$) #-}
  dualDoc _ h = h
  {-# INLINE CONLIKE dualDoc #-}
