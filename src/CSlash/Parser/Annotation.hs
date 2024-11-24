{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

module CSlash.Parser.Annotation (
  AnnKeywordId(..),
  EpToken(..), EpUniToken(..),
  getEpTokenSrcSpan,
  EpLayout(..),
  EpaComment(..), EpaCommentTok(..),
  IsUnicodeSyntax(..),
  unicodeAnn,

  AddEpAnn(..),
  EpaLocation, EpaLocation'(..), epaLocationRealSrcSpan,
  TokenLocation(..),
  DeltaPos(..), deltaPos, getDeltaLine,

  EpAnn(..), Anchor,
  anchor,
  spanAsAnchor, realSpanAsAnchor,
  noSpanAnchor,
  NoAnn(..),

  EpAnnComments(..), LEpaComment, NoCommentsLocation, NoComments(..), emptyComments,
  epaToNoCommentsLocation, noCommentsToEpaLocation,
  getFollowingComments, setFollowingComments, setPriorComments,
  EpAnnCO,

  LocatedA, LocatedL, LocatedC, LocatedN, LocatedAn, LocatedP,
  SrcSpanAnnA, SrcSpanAnnL, SrcSpanAnnP, SrcSpanAnnC, SrcSpanAnnN,
  LocatedE,

  AnnListItem(..), AnnList(..),
  AnnParen(..), ParenType(..), parenTypeKws,
  AnnPragma(..),
  AnnContext(..),
  NameAnn(..), NameAdornment(..),
  NoEpAnns(..),
  AnnSortKey(..), DeclTag(..), BindTag(..),

  TrailingAnn(..), trailingAnnToAddEpAnn,
  addTrailingAnnToA, addTrailingAnnToL, addTrailingCommaToN,
  noTrailingN,

  l2l, la2la,
  reLoc,
  HasLoc(..), getHasLocList,

  srcSpan2e, realSrcSpan,

  reAnnL, reAnnC,
  addAnns, addAnnsA, widenSpan, widenAnchor, widenAnchorS, widenLocatedAn,
  listLocation,

  getLocAnn,
  epAnnAnns,
  annParen2AddEpAnn,
  epAnnComments,

  sortLocatedA,
  mapLocA,
  combineLocsA,
  combineSrcSpansA,
  addCLocA,

  HasAnnotation(..),
  locA,
  noLocA,
  getLocA,
  noSrcSpanA,

  noComments, comment, addCommentsToEpAnn, setCommentsEpAnn,
  transferAnnsA, transferAnnsOnlyA, transferCommentsOnlyA,
  transferPriorCommentsA, transferFollowingA,
  commentsOnlyA, removeCommentsA,

  placeholderRealSpan,
  ) where

import Data.Data
import Data.Function (on)
import Data.List (sortBy, foldl1')
import Data.Semigroup
import CSlash.Data.FastString
import GHC.TypeLits (Symbol, KnownSymbol)
import CSlash.Types.Name
import CSlash.Types.SrcLoc
-- import CSlash.Hs.DocString
import CSlash.Utils.Outputable hiding ( (<>) )
import CSlash.Utils.Panic
import qualified CSlash.Data.Strict as Strict
import CSlash.Types.SourceText (SourceText (NoSourceText))

data AnnKeywordId
    = AnnAnyclass
    | AnnAs
    | AnnBang  -- ^ '!'
    | AnnBackquote -- ^ '`'
    | AnnBy
    | AnnCase -- ^ case or lambda case
    | AnnCases -- ^ lambda cases
    | AnnClass
    | AnnClose -- ^  '\#)' or '\#-}'  etc
    | AnnCloseB -- ^ '|)'
    | AnnCloseBU -- ^ '|)', unicode variant
    | AnnCloseC -- ^ '}'
    | AnnCloseQ  -- ^ '|]'
    | AnnCloseQU -- ^ '|]', unicode variant
    | AnnCloseP -- ^ ')'
    | AnnClosePH -- ^ '\#)'
    | AnnCloseS -- ^ ']'
    | AnnColon
    | AnnComma -- ^ as a list separator
    | AnnCommaTuple -- ^ in a RdrName for a tuple
    | AnnDarrow -- ^ '=>'
    | AnnDarrowU -- ^ '=>', unicode variant
    | AnnData
    | AnnDcolon -- ^ '::'
    | AnnDcolonU -- ^ '::', unicode variant
    | AnnDefault
    | AnnDeriving
    | AnnDo
    | AnnDot    -- ^ '.'
    | AnnDotdot -- ^ '..'
    | AnnElse
    | AnnEqual
    | AnnExport
    | AnnFamily
    | AnnForall
    | AnnForallU -- ^ Unicode variant
    | AnnForeign
    | AnnFunId -- ^ for function name in matches where there are
               -- multiple equations for the function.
    | AnnGroup
    | AnnHeader -- ^ for CType
    | AnnHiding
    | AnnIf
    | AnnImport
    | AnnIn
    | AnnInfix -- ^ 'infix' or 'infixl' or 'infixr'
    | AnnInstance
    | AnnLam        -- ^ '\\'
    | AnnTyLam      -- ^ '/\\'
    | AnnLarrow     -- ^ '<-'
    | AnnLarrowU    -- ^ '<-', unicode variant
    | AnnLet
    | AnnLollyU     -- ^ The '⊸' unicode arrow
    | AnnMdo
    | AnnMinus -- ^ '-'
    | AnnModule
    | AnnNewtype
    | AnnName -- ^ where a name loses its location in the AST, this carries it
    | AnnOf
    | AnnOpen    -- ^ '{-\# DEPRECATED' etc. Opening of pragmas where
                 -- the capitalisation of the string can be changed by
                 -- the user. The actual text used is stored in a
                 -- 'SourceText' on the relevant pragma item.
    | AnnOpenB   -- ^ '(|'
    | AnnOpenBU  -- ^ '(|', unicode variant
    | AnnOpenC   -- ^ '{'
    | AnnOpenE   -- ^ '[e|' or '[e||'
    | AnnOpenEQ  -- ^ '[|'
    | AnnOpenEQU -- ^ '[|', unicode variant
    | AnnOpenP   -- ^ '('
    | AnnOpenS   -- ^ '['
    | AnnOpenPH  -- ^ '(\#'
    | AnnDollar          -- ^ prefix '$'   -- TemplateHaskell
    | AnnDollarDollar    -- ^ prefix '$$'  -- TemplateHaskell
    | AnnPackageName
    | AnnPattern
    | AnnPercent    -- ^ '%'  -- for HsExplicitMult
    | AnnPercentOne -- ^ '%1' -- for HsLinearArrow
    | AnnProc
    | AnnQualified
    | AnnRarrow -- ^ '->'
    | AnnRarrowU -- ^ '->', unicode variant
    | AnnRec
    | AnnRole
    | AnnSafe
    | AnnSemi -- ^ ';'
    | AnnSimpleQuote -- ^ '''
    | AnnSignature
    | AnnStatic -- ^ 'static'
    | AnnStock
    | AnnThen
    | AnnThTyQuote -- ^ double '''
    | AnnTilde -- ^ '~'
    | AnnType
    | AnnUnit -- ^ '()' for types
    | AnnUsing
    | AnnVal  -- ^ e.g. INTEGER
    | AnnValStr  -- ^ String value, will need quotes when output
    | AnnVbar -- ^ '|'
    | AnnVia -- ^ 'via'
    | AnnWhere
    | Annlarrowtail -- ^ '-<'
    | AnnlarrowtailU -- ^ '-<', unicode variant
    | Annrarrowtail -- ^ '->'
    | AnnrarrowtailU -- ^ '->', unicode variant
    | AnnLarrowtail -- ^ '-<<'
    | AnnLarrowtailU -- ^ '-<<', unicode variant
    | AnnRarrowtail -- ^ '>>-'
    | AnnRarrowtailU -- ^ '>>-', unicode variant
    deriving (Eq, Ord, Data, Show)

instance Outputable AnnKeywordId where
  ppr x = text (show x)

data IsUnicodeSyntax = UnicodeSyntax | NormalSyntax
    deriving (Eq, Ord, Data, Show)

unicodeAnn :: AnnKeywordId -> AnnKeywordId
unicodeAnn AnnForall     = AnnForallU
unicodeAnn AnnDcolon     = AnnDcolonU
unicodeAnn AnnLarrow     = AnnLarrowU
unicodeAnn AnnRarrow     = AnnRarrowU
unicodeAnn AnnDarrow     = AnnDarrowU
unicodeAnn Annlarrowtail = AnnlarrowtailU
unicodeAnn Annrarrowtail = AnnrarrowtailU
unicodeAnn AnnLarrowtail = AnnLarrowtailU
unicodeAnn AnnRarrowtail = AnnRarrowtailU
unicodeAnn AnnOpenB      = AnnOpenBU
unicodeAnn AnnCloseB     = AnnCloseBU
unicodeAnn AnnOpenEQ     = AnnOpenEQU
unicodeAnn AnnCloseQ     = AnnCloseQU
unicodeAnn ann           = ann


data EpToken (tok :: Symbol)
  = NoEpTok
  | EpTok !EpaLocation

data EpUniToken (tok :: Symbol) (utok :: Symbol)
  = NoEpUniTok
  | EpUniTok !EpaLocation !IsUnicodeSyntax

deriving instance Eq (EpToken tok)
deriving instance KnownSymbol tok => Data (EpToken tok)
deriving instance (KnownSymbol tok, KnownSymbol utok) => Data (EpUniToken tok utok)

getEpTokenSrcSpan :: EpToken tok -> SrcSpan
getEpTokenSrcSpan NoEpTok = noSrcSpan
getEpTokenSrcSpan (EpTok EpaDelta{}) = noSrcSpan
getEpTokenSrcSpan (EpTok (EpaSpan span)) = span

data EpLayout 
  = EpExplicitBraces !(EpToken "{") !(EpToken "}")
  | EpVirtualBraces !Int
  | EpNoLayout

deriving instance Data EpLayout

data EpaComment =
  EpaComment
    { ac_tok :: EpaCommentTok
    , ac_prior_tok :: RealSrcSpan
    }
    deriving (Eq, Data, Show)

data EpaCommentTok 
  --  = EpaDocComment      HsDocString
  = EpaDocOptions      String     
  | EpaLineComment     String     
  | EpaBlockComment    String     
    deriving (Eq, Data, Show)

instance Outputable EpaComment where
  ppr x = text (show x)

data AddEpAnn = AddEpAnn AnnKeywordId EpaLocation deriving (Data,Eq)

type EpaLocation = EpaLocation' [LEpaComment]

epaToNoCommentsLocation :: EpaLocation -> NoCommentsLocation
epaToNoCommentsLocation (EpaSpan ss) = EpaSpan ss
epaToNoCommentsLocation (EpaDelta dp []) = EpaDelta dp NoComments
epaToNoCommentsLocation (EpaDelta _ _ ) = panic "epaToNoCommentsLocation"

noCommentsToEpaLocation :: NoCommentsLocation -> EpaLocation
noCommentsToEpaLocation (EpaSpan ss) = EpaSpan ss
noCommentsToEpaLocation (EpaDelta dp NoComments) = EpaDelta dp []

data TokenLocation = NoTokenLoc | TokenLoc !EpaLocation
               deriving (Data,Eq)

instance Outputable a => Outputable (GenLocated TokenLocation a) where
  ppr (L _ x) = ppr x

epaLocationRealSrcSpan :: EpaLocation -> RealSrcSpan
epaLocationRealSrcSpan (EpaSpan (RealSrcSpan r _)) = r
epaLocationRealSrcSpan _ = panic "epaLocationRealSrcSpan"

instance Outputable AddEpAnn where
  ppr (AddEpAnn kw ss) = text "AddEpAnn" <+> ppr kw <+> ppr ss

data EpAnn ann
  = EpAnn { entry   :: !Anchor
           , anns     :: !ann -- ^ Annotations added by the Parser
           , comments :: !EpAnnComments
           }
        deriving (Data, Eq, Functor)

type Anchor = EpaLocation

anchor :: (EpaLocation' a) -> RealSrcSpan
anchor (EpaSpan (RealSrcSpan r _)) = r
anchor _ = panic "anchor"

spanAsAnchor :: SrcSpan -> (EpaLocation' a)
spanAsAnchor ss  = EpaSpan ss

realSpanAsAnchor :: RealSrcSpan -> (EpaLocation' a)
realSpanAsAnchor s = EpaSpan (RealSrcSpan s Strict.Nothing)

noSpanAnchor :: (NoAnn a) => (EpaLocation' a)
noSpanAnchor =  EpaDelta (SameLine 0) noAnn

data EpAnnComments = EpaComments
                        { priorComments :: ![LEpaComment] }
                    | EpaCommentsBalanced
                        { priorComments :: ![LEpaComment]
                        , followingComments :: ![LEpaComment] }
        deriving (Data, Eq)

type LEpaComment = GenLocated NoCommentsLocation EpaComment

emptyComments :: EpAnnComments
emptyComments = EpaComments []

type LocatedA = GenLocated SrcSpanAnnA
type LocatedN = GenLocated SrcSpanAnnN

type LocatedL = GenLocated SrcSpanAnnL
type LocatedP = GenLocated SrcSpanAnnP
type LocatedC = GenLocated SrcSpanAnnC

type SrcSpanAnnA = EpAnn AnnListItem
type SrcSpanAnnN = EpAnn NameAnn

type SrcSpanAnnL = EpAnn AnnList
type SrcSpanAnnP = EpAnn AnnPragma
type SrcSpanAnnC = EpAnn AnnContext

type LocatedE = GenLocated EpaLocation

type LocatedAn an = GenLocated (EpAnn an)

data TrailingAnn
  = AddSemiAnn    { ta_location :: EpaLocation }  -- ^ Trailing ';'
  | AddCommaAnn   { ta_location :: EpaLocation }  -- ^ Trailing ','
  | AddVbarAnn    { ta_location :: EpaLocation }  -- ^ Trailing '|'
  | AddDarrowAnn  { ta_location :: EpaLocation }  -- ^ Trailing '=>'
  | AddDarrowUAnn { ta_location :: EpaLocation }  -- ^ Trailing  "⇒"
  deriving (Data, Eq)

instance Outputable TrailingAnn where
  ppr (AddSemiAnn ss)    = text "AddSemiAnn"    <+> ppr ss
  ppr (AddCommaAnn ss)   = text "AddCommaAnn"   <+> ppr ss
  ppr (AddVbarAnn ss)    = text "AddVbarAnn"    <+> ppr ss
  ppr (AddDarrowAnn ss)  = text "AddDarrowAnn"  <+> ppr ss
  ppr (AddDarrowUAnn ss) = text "AddDarrowUAnn" <+> ppr ss

data AnnListItem
  = AnnListItem {
      lann_trailing  :: [TrailingAnn]
      }
  deriving (Data, Eq)

data AnnList
  = AnnList {
      al_anchor    :: Maybe Anchor,
      al_open      :: Maybe AddEpAnn,
      al_close     :: Maybe AddEpAnn,
      al_rest      :: [AddEpAnn], 
      al_trailing  :: [TrailingAnn]
      } deriving (Data,Eq)

data AnnParen
  = AnnParen {
      ap_adornment :: ParenType,
      ap_open      :: EpaLocation,
      ap_close     :: EpaLocation
      } deriving (Data)

data ParenType
  = AnnParens       -- ^ '(', ')'
  | AnnParensHash   -- ^ '(#', '#)'
  | AnnParensSquare -- ^ '[', ']'
  deriving (Eq, Ord, Data, Show)

parenTypeKws :: ParenType -> (AnnKeywordId, AnnKeywordId)
parenTypeKws AnnParens       = (AnnOpenP, AnnCloseP)
parenTypeKws AnnParensHash   = (AnnOpenPH, AnnClosePH)
parenTypeKws AnnParensSquare = (AnnOpenS, AnnCloseS)

data AnnContext
  = AnnContext {
      ac_darrow    :: Maybe (IsUnicodeSyntax, EpaLocation),
      ac_open      :: [EpaLocation],
      ac_close     :: [EpaLocation] 
      } deriving (Data)

data NameAnn
  -- nUsed for a name with an adornment, so '`foo`', '(bar)'
  = NameAnn {
      nann_adornment :: NameAdornment,
      nann_open      :: EpaLocation,
      nann_name      :: EpaLocation,
      nann_close     :: EpaLocation,
      nann_trailing  :: [TrailingAnn]
      }
  -- Used for @(,,,)@, or @(#,,,#)#
  | NameAnnCommas {
      nann_adornment :: NameAdornment,
      nann_open      :: EpaLocation,
      nann_commas    :: [EpaLocation],
      nann_close     :: EpaLocation,
      nann_trailing  :: [TrailingAnn]
      }
  -- Used for @(# | | #)@
  | NameAnnBars {
      nann_adornment :: NameAdornment,
      nann_open      :: EpaLocation,
      nann_bars      :: [EpaLocation],
      nann_close     :: EpaLocation,
      nann_trailing  :: [TrailingAnn]
      }
  -- Used for @()@, @(##)@, @[]@
  | NameAnnOnly {
      nann_adornment :: NameAdornment,
      nann_open      :: EpaLocation,
      nann_close     :: EpaLocation,
      nann_trailing  :: [TrailingAnn]
      }
  -- Used for @->@, as an identifier
  | NameAnnRArrow {
      nann_unicode   :: Bool,
      nann_mopen     :: Maybe EpaLocation,
      nann_name      :: EpaLocation,
      nann_mclose    :: Maybe EpaLocation,
      nann_trailing  :: [TrailingAnn]
      }
  | NameAnnUnArrow {
      nann_mopen     :: Maybe EpaLocation,
      nann_name      :: EpaLocation,
      nann_mclose    :: Maybe EpaLocation,
      nann_trailing  :: [TrailingAnn]
      }
  | NameAnnAffArrow {
      nann_mopen     :: Maybe EpaLocation,
      nann_name      :: EpaLocation,
      nann_mclose    :: Maybe EpaLocation,
      nann_trailing  :: [TrailingAnn]
      }
  | NameAnnLinArrow {
      nann_mopen     :: Maybe EpaLocation,
      nann_name      :: EpaLocation,
      nann_mclose    :: Maybe EpaLocation,
      nann_trailing  :: [TrailingAnn]
      }
  -- Used for an item with a leading @'@. The annotation for
  -- unquoted item is stored in 'nann_quoted'.
  | NameAnnQuote {
      nann_quote     :: EpaLocation,
      nann_quoted    :: SrcSpanAnnN,
      nann_trailing  :: [TrailingAnn]
      }
  -- Used when adding a 'TrailingAnn' to an existing 'LocatedN'
  -- which has no Api Annotation (via the 'EpAnnNotUsed' constructor.
  | NameAnnTrailing {
      nann_trailing  :: [TrailingAnn]
      }
  deriving (Data, Eq)

data NameAdornment
  = NameParens -- ^ '(' ')'
  | NameParensHash -- ^ '(#' '#)'
  | NameBackquotes -- ^ '`'
  | NameSquare -- ^ '[' ']'
  deriving (Eq, Ord, Data)

data AnnPragma
  = AnnPragma {
      apr_open      :: AddEpAnn,
      apr_close     :: AddEpAnn,
      apr_rest      :: [AddEpAnn]
      } deriving (Data,Eq)

data AnnSortKey tag
  = NoAnnSortKey
  | AnnSortKey [tag]
  deriving (Data, Eq)

data BindTag
  = BindTag
  | SigDTag
  deriving (Eq,Data,Ord,Show)

data DeclTag
  = ClsMethodTag
  | ClsSigTag
  | ClsAtTag
  | ClsAtdTag
  deriving (Eq,Data,Ord,Show)

trailingAnnToAddEpAnn :: TrailingAnn -> AddEpAnn
trailingAnnToAddEpAnn (AddSemiAnn ss)    = AddEpAnn AnnSemi ss
trailingAnnToAddEpAnn (AddCommaAnn ss)   = AddEpAnn AnnComma ss
trailingAnnToAddEpAnn (AddVbarAnn ss)    = AddEpAnn AnnVbar ss
trailingAnnToAddEpAnn (AddDarrowUAnn ss) = AddEpAnn AnnDarrowU ss
trailingAnnToAddEpAnn (AddDarrowAnn ss)  = AddEpAnn AnnDarrow ss

addTrailingAnnToL :: TrailingAnn -> EpAnnComments
                  -> EpAnn AnnList -> EpAnn AnnList
addTrailingAnnToL t cs n = n { anns = addTrailing (anns n)
                               , comments = comments n <> cs }
  where
    addTrailing n = n { al_trailing = al_trailing n ++ [t]}

addTrailingAnnToA :: TrailingAnn -> EpAnnComments
                  -> EpAnn AnnListItem -> EpAnn AnnListItem
addTrailingAnnToA t cs n = n { anns = addTrailing (anns n)
                               , comments = comments n <> cs }
  where
    addTrailing n = n { lann_trailing = lann_trailing n ++ [t] }

addTrailingCommaToN :: EpAnn NameAnn -> EpaLocation -> EpAnn NameAnn
addTrailingCommaToN  n l = n { anns = addTrailing (anns n) l }
  where
    addTrailing :: NameAnn -> EpaLocation -> NameAnn
    addTrailing n l = n { nann_trailing = nann_trailing n ++ [AddCommaAnn l]}

noTrailingN :: SrcSpanAnnN -> SrcSpanAnnN
noTrailingN s = s { anns = (anns s) { nann_trailing = [] } }

l2l :: (HasLoc a, HasAnnotation b) => a -> b
l2l a = noAnnSrcSpan (getHasLoc a)

la2la :: (HasLoc l, HasAnnotation l2) => GenLocated l a -> GenLocated l2 a
la2la (L la a) = L (noAnnSrcSpan (getHasLoc la)) a

locA :: (HasLoc a) => a -> SrcSpan
locA = getHasLoc

reLoc :: (HasLoc (GenLocated a e), HasAnnotation b)
      => GenLocated a e -> GenLocated b e
reLoc (L la a) = L (noAnnSrcSpan $ locA (L la a) ) a

class HasAnnotation e where
  noAnnSrcSpan :: SrcSpan -> e

instance HasAnnotation SrcSpan where
  noAnnSrcSpan l = l

instance HasAnnotation EpaLocation where
  noAnnSrcSpan l = EpaSpan l

instance (NoAnn ann) => HasAnnotation (EpAnn ann) where
  noAnnSrcSpan l = EpAnn (spanAsAnchor l) noAnn emptyComments

noLocA :: (HasAnnotation e) => a -> GenLocated e a
noLocA = L (noAnnSrcSpan noSrcSpan)

getLocA :: (HasLoc a) => GenLocated a e -> SrcSpan
getLocA = getHasLoc

noSrcSpanA :: (HasAnnotation e) => e
noSrcSpanA = noAnnSrcSpan noSrcSpan

class NoAnn a where
  -- | equivalent of `mempty`, but does not need Semigroup
  noAnn :: a

class HasLoc a where
  getHasLoc :: a -> SrcSpan

instance (HasLoc l) => HasLoc (GenLocated l a) where
  getHasLoc (L l _) = getHasLoc l

instance HasLoc SrcSpan where
  getHasLoc l = l

instance (HasLoc a) => (HasLoc (Maybe a)) where
  getHasLoc (Just a) = getHasLoc a
  getHasLoc Nothing = noSrcSpan

instance HasLoc (EpAnn a) where
  getHasLoc (EpAnn l _ _) = getHasLoc l

instance HasLoc EpaLocation where
  getHasLoc (EpaSpan l) = l
  getHasLoc (EpaDelta _ _) = noSrcSpan

getHasLocList :: HasLoc a => [a] -> SrcSpan
getHasLocList [] = noSrcSpan
getHasLocList xs = foldl1' combineSrcSpans $ map getHasLoc xs

realSrcSpan :: SrcSpan -> RealSrcSpan
realSrcSpan (RealSrcSpan s _) = s
realSrcSpan _ = mkRealSrcSpan l l -- AZ temporary
  where
    l = mkRealSrcLoc (fsLit "realSrcSpan") (-1) (-1)

srcSpan2e :: SrcSpan -> EpaLocation
srcSpan2e ss@(RealSrcSpan _ _) = EpaSpan ss
srcSpan2e span = EpaSpan (RealSrcSpan (realSrcSpan span) Strict.Nothing)

reAnnC :: AnnContext -> EpAnnComments -> Located a -> LocatedC a
reAnnC anns cs (L l a) = L (EpAnn (spanAsAnchor l) anns cs) a

reAnnL :: ann -> EpAnnComments -> Located e -> GenLocated (EpAnn ann) e
reAnnL anns cs (L l a) = L (EpAnn (spanAsAnchor l) anns cs) a

getLocAnn :: Located a  -> SrcSpanAnnA
getLocAnn (L l _) = noAnnSrcSpan l

addAnns :: EpAnn [AddEpAnn] -> [AddEpAnn] -> EpAnnComments -> EpAnn [AddEpAnn]
addAnns (EpAnn l as1 cs) as2 cs2
  = EpAnn (widenAnchor l (as1 ++ as2)) (as1 ++ as2) (cs <> cs2)

addAnnsA :: SrcSpanAnnA -> [TrailingAnn] -> EpAnnComments -> SrcSpanAnnA
addAnnsA (EpAnn l as1 cs) as2 cs2
  = EpAnn l (AnnListItem (lann_trailing as1 ++ as2)) (cs <> cs2)

widenSpan :: SrcSpan -> [AddEpAnn] -> SrcSpan
widenSpan s as = foldl combineSrcSpans s (go as)
  where
    go [] = []
    go (AddEpAnn _ (EpaSpan (RealSrcSpan s mb)):rest) = RealSrcSpan s mb : go rest
    go (AddEpAnn _ (EpaSpan _):rest) = go rest
    go (AddEpAnn _ (EpaDelta _ _):rest) = go rest

widenRealSpan :: RealSrcSpan -> [AddEpAnn] -> RealSrcSpan
widenRealSpan s as = foldl combineRealSrcSpans s (go as)
  where
    go [] = []
    go (AddEpAnn _ (EpaSpan (RealSrcSpan s _)):rest) = s : go rest
    go (AddEpAnn _ _:rest) = go rest

realSpanFromAnns :: [AddEpAnn] -> Strict.Maybe RealSrcSpan
realSpanFromAnns as = go Strict.Nothing as
  where
    combine Strict.Nothing r  = Strict.Just r
    combine (Strict.Just l) r = Strict.Just $ combineRealSrcSpans l r

    go acc [] = acc
    go acc (AddEpAnn _ (EpaSpan (RealSrcSpan s _b)):rest) = go (combine acc s) rest
    go acc (AddEpAnn _ _             :rest) = go acc rest

bufSpanFromAnns :: [AddEpAnn] -> Strict.Maybe BufSpan
bufSpanFromAnns as =  go Strict.Nothing as
  where
    combine Strict.Nothing r  = Strict.Just r
    combine (Strict.Just l) r = Strict.Just $ combineBufSpans l r

    go acc [] = acc
    go acc (AddEpAnn _ (EpaSpan (RealSrcSpan _ (Strict.Just mb))):rest) = go (combine acc mb) rest
    go acc (AddEpAnn _ _:rest) = go acc rest

listLocation :: [LocatedAn an a] -> EpaLocation
listLocation as = EpaSpan (go noSrcSpan as)
  where
    combine l r = combineSrcSpans l r

    go acc [] = acc
    go acc (L (EpAnn (EpaSpan s) _ _) _ : rest) = go (combine acc s) rest
    go acc (_:rest) = go acc rest

widenAnchor :: Anchor -> [AddEpAnn] -> Anchor
widenAnchor (EpaSpan (RealSrcSpan s mb)) as
  = EpaSpan (RealSrcSpan (widenRealSpan s as) (liftA2 combineBufSpans mb  (bufSpanFromAnns as)))
widenAnchor (EpaSpan us) _ = EpaSpan us
widenAnchor a@(EpaDelta _ _) as = case (realSpanFromAnns as) of
                                    Strict.Nothing -> a
                                    Strict.Just r -> EpaSpan (RealSrcSpan r Strict.Nothing)

widenAnchorS :: Anchor -> SrcSpan -> Anchor
widenAnchorS (EpaSpan (RealSrcSpan s mbe)) (RealSrcSpan r mbr)
  = EpaSpan (RealSrcSpan (combineRealSrcSpans s r) (liftA2 combineBufSpans mbe mbr))
widenAnchorS (EpaSpan us) _ = EpaSpan us
widenAnchorS (EpaDelta _ _) (RealSrcSpan r mb) = EpaSpan (RealSrcSpan r mb)
widenAnchorS anc _ = anc

widenLocatedAn :: EpAnn an -> [AddEpAnn] -> EpAnn an
widenLocatedAn (EpAnn (EpaSpan l) a cs) as = EpAnn (spanAsAnchor l') a cs
  where
    l' = widenSpan l as
widenLocatedAn (EpAnn anc a cs) _as = EpAnn anc a cs

epAnnAnns :: EpAnn [AddEpAnn] -> [AddEpAnn]
epAnnAnns (EpAnn _ anns _) = anns

annParen2AddEpAnn :: AnnParen -> [AddEpAnn]
annParen2AddEpAnn (AnnParen pt o c)
  = [AddEpAnn ai o, AddEpAnn ac c]
  where
    (ai,ac) = parenTypeKws pt

epAnnComments :: EpAnn an -> EpAnnComments
epAnnComments (EpAnn _ _ cs) = cs

sortLocatedA :: (HasLoc (EpAnn a)) => [GenLocated (EpAnn a) e] -> [GenLocated (EpAnn a) e]
sortLocatedA = sortBy (leftmost_smallest `on` getLocA)

mapLocA :: (NoAnn ann) => (a -> b) -> GenLocated SrcSpan a -> GenLocated (EpAnn ann) b
mapLocA f (L l a) = L (noAnnSrcSpan l) (f a)

combineLocsA :: Semigroup a => GenLocated (EpAnn a) e1 -> GenLocated (EpAnn a) e2 -> EpAnn a
combineLocsA (L a _) (L b _) = combineSrcSpansA a b

combineSrcSpansA :: Semigroup a => EpAnn a -> EpAnn a -> EpAnn a
combineSrcSpansA aa ab = aa <> ab

addCLocA :: (HasLoc a, HasLoc b, HasAnnotation l)
         => a -> b -> c -> GenLocated l c
addCLocA a b c = L (noAnnSrcSpan $ combineSrcSpans (getHasLoc a) (getHasLoc b)) c

getFollowingComments :: EpAnnComments -> [LEpaComment]
getFollowingComments (EpaComments _) = []
getFollowingComments (EpaCommentsBalanced _ cs) = cs

setFollowingComments :: EpAnnComments -> [LEpaComment] -> EpAnnComments
setFollowingComments (EpaComments ls) cs           = EpaCommentsBalanced ls cs
setFollowingComments (EpaCommentsBalanced ls _) cs = EpaCommentsBalanced ls cs

setPriorComments :: EpAnnComments -> [LEpaComment] -> EpAnnComments
setPriorComments (EpaComments _) cs            = EpaComments cs
setPriorComments (EpaCommentsBalanced _ ts) cs = EpaCommentsBalanced cs ts

type EpAnnCO = EpAnn NoEpAnns

data NoEpAnns = NoEpAnns
  deriving (Data,Eq,Ord)

noComments ::EpAnnCO
noComments = EpAnn noSpanAnchor NoEpAnns emptyComments

placeholderRealSpan :: RealSrcSpan
placeholderRealSpan = realSrcLocSpan (mkRealSrcLoc (mkFastString "placeholder") (-1) (-1))

comment :: RealSrcSpan -> EpAnnComments -> EpAnnCO
comment loc cs = EpAnn (EpaSpan (RealSrcSpan loc Strict.Nothing)) NoEpAnns cs

addCommentsToEpAnn :: (NoAnn ann) => EpAnn ann -> EpAnnComments -> EpAnn ann
addCommentsToEpAnn (EpAnn a an cs) cs' = EpAnn a an (cs <> cs')

setCommentsEpAnn :: (NoAnn ann) => EpAnn ann -> EpAnnComments -> EpAnn ann
setCommentsEpAnn (EpAnn a an _) cs = (EpAnn a an cs)

transferAnnsA :: SrcSpanAnnA -> SrcSpanAnnA -> (SrcSpanAnnA,  SrcSpanAnnA)
transferAnnsA (EpAnn a an cs) (EpAnn a' an' cs')
  = (EpAnn a noAnn emptyComments, EpAnn a' (an' <> an) (cs' <> cs))

transferFollowingA :: SrcSpanAnnA -> SrcSpanAnnA -> (SrcSpanAnnA,  SrcSpanAnnA)
transferFollowingA (EpAnn a1 an1 cs1) (EpAnn a2 an2 cs2)
  = (EpAnn a1 noAnn cs1', EpAnn a2 (an1 <> an2) cs2')
  where
    pc = priorComments cs1
    fc = getFollowingComments cs1
    cs1' = setPriorComments emptyComments pc
    cs2' = setFollowingComments cs2 fc

transferAnnsOnlyA :: SrcSpanAnnA -> SrcSpanAnnA -> (SrcSpanAnnA,  SrcSpanAnnA)
transferAnnsOnlyA (EpAnn a an cs) (EpAnn a' an' cs')
  = (EpAnn a noAnn cs, EpAnn a' (an' <> an) cs')

transferCommentsOnlyA :: EpAnn a -> EpAnn b -> (EpAnn a,  EpAnn b)
transferCommentsOnlyA (EpAnn a an cs) (EpAnn a' an' cs')
  = (EpAnn a an emptyComments, EpAnn a' an' (cs <> cs'))

transferPriorCommentsA :: SrcSpanAnnA -> SrcSpanAnnA -> (SrcSpanAnnA,  SrcSpanAnnA)
transferPriorCommentsA (EpAnn a1 an1 cs1) (EpAnn a2 an2 cs2)
  = (EpAnn a1 an1 cs1', EpAnn a2 an2 cs2')
  where
    pc = priorComments cs1
    fc = getFollowingComments cs1
    cs1' = setFollowingComments emptyComments fc
    cs2' = setPriorComments cs2 (priorComments cs2 <> pc)

commentsOnlyA :: NoAnn ann => EpAnn ann -> EpAnn ann
commentsOnlyA (EpAnn a _ cs) = EpAnn a noAnn cs

removeCommentsA :: EpAnn ann -> EpAnn ann
removeCommentsA (EpAnn a an _) = EpAnn a an emptyComments

instance (Semigroup a) => Semigroup (EpAnn a) where
  (EpAnn l1 a1 b1) <> (EpAnn l2 a2 b2) = EpAnn (l1 <> l2) (a1 <> a2) (b1 <> b2)

instance Semigroup EpaLocation where
  EpaSpan s1       <> EpaSpan s2        = EpaSpan (combineSrcSpans s1 s2)
  EpaSpan s1       <> _                 = EpaSpan s1
  _                <> EpaSpan s2        = EpaSpan s2
  EpaDelta dp1 cs1 <> EpaDelta _dp2 cs2 = EpaDelta dp1 (cs1<>cs2)

instance Semigroup EpAnnComments where
  EpaComments cs1 <> EpaComments cs2 = EpaComments (cs1 ++ cs2)
  EpaComments cs1 <> EpaCommentsBalanced cs2 as2 = EpaCommentsBalanced (cs1 ++ cs2) as2
  EpaCommentsBalanced cs1 as1 <> EpaComments cs2 = EpaCommentsBalanced (cs1 ++ cs2) as1
  EpaCommentsBalanced cs1 as1 <> EpaCommentsBalanced cs2 as2 = EpaCommentsBalanced (cs1 ++ cs2) (as1++as2)

instance Semigroup AnnListItem where
  (AnnListItem l1) <> (AnnListItem l2) = AnnListItem (l1 <> l2)

instance Semigroup (AnnSortKey tag) where
  NoAnnSortKey <> x = x
  x <> NoAnnSortKey = x
  AnnSortKey ls1 <> AnnSortKey ls2 = AnnSortKey (ls1 <> ls2)

instance Monoid (AnnSortKey tag) where
  mempty = NoAnnSortKey

instance NoAnn EpaLocation where
  noAnn = EpaDelta (SameLine 0) []

instance NoAnn AnnKeywordId where
  noAnn = Annlarrowtail  {- gotta pick one -}

instance NoAnn AddEpAnn where
  noAnn = AddEpAnn noAnn noAnn

instance NoAnn [a] where
  noAnn = []

instance NoAnn (Maybe a) where
  noAnn = Nothing

instance (NoAnn a, NoAnn b) => NoAnn (a, b) where
  noAnn = (noAnn, noAnn)

instance NoAnn Bool where
  noAnn = False

instance (NoAnn ann) => NoAnn (EpAnn ann) where
  noAnn = EpAnn noSpanAnchor noAnn emptyComments

instance NoAnn NoEpAnns where
  noAnn = NoEpAnns

instance NoAnn AnnListItem where
  noAnn = AnnListItem []

instance NoAnn AnnContext where
  noAnn = AnnContext Nothing [] []

instance NoAnn AnnList where
  noAnn = AnnList Nothing Nothing Nothing [] []

instance NoAnn NameAnn where
  noAnn = NameAnnTrailing []

instance NoAnn AnnPragma where
  noAnn = AnnPragma noAnn noAnn []

instance NoAnn AnnParen where
  noAnn = AnnParen AnnParens noAnn noAnn

instance NoAnn (EpToken s) where
  noAnn = NoEpTok

instance NoAnn (EpUniToken s t) where
  noAnn = NoEpUniTok

instance NoAnn SourceText where
  noAnn = NoSourceText

instance (Outputable a) => Outputable (EpAnn a) where
  ppr (EpAnn l a c)  = text "EpAnn" <+> ppr l <+> ppr a <+> ppr c

instance Outputable NoEpAnns where
  ppr NoEpAnns = text "NoEpAnns"

instance Outputable (GenLocated NoCommentsLocation EpaComment) where
  ppr (L l c) = text "L" <+> ppr l <+> ppr c

instance Outputable EpAnnComments where
  ppr (EpaComments cs) = text "EpaComments" <+> ppr cs
  ppr (EpaCommentsBalanced cs ts) = text "EpaCommentsBalanced" <+> ppr cs <+> ppr ts

instance (NamedThing (Located a)) => NamedThing (LocatedAn an a) where
  getName (L l a) = getName (L (locA l) a)

instance Outputable AnnContext where
  ppr (AnnContext a o c) = text "AnnContext" <+> ppr a <+> ppr o <+> ppr c

instance Outputable BindTag where
  ppr tag = text $ show tag

instance Outputable DeclTag where
  ppr tag = text $ show tag

instance Outputable tag => Outputable (AnnSortKey tag) where
  ppr NoAnnSortKey    = text "NoAnnSortKey"
  ppr (AnnSortKey ls) = text "AnnSortKey" <+> ppr ls

instance Outputable IsUnicodeSyntax where
  ppr = text . show

instance (Outputable a, Outputable e)
     => Outputable (GenLocated (EpAnn a) e) where
  ppr = pprLocated

instance (Outputable a, OutputableBndr e)
     => OutputableBndr (GenLocated (EpAnn a) e) where
  pprInfixOcc = pprInfixOcc . unLoc
  pprPrefixOcc = pprPrefixOcc . unLoc

instance (Outputable e)
     => Outputable (GenLocated EpaLocation e) where
  ppr = pprLocated

instance Outputable ParenType where
  ppr t = text (show t)

instance Outputable AnnListItem where
  ppr (AnnListItem ts) = text "AnnListItem" <+> ppr ts

instance Outputable NameAdornment where
  ppr NameParens     = text "NameParens"
  ppr NameParensHash = text "NameParensHash"
  ppr NameBackquotes = text "NameBackquotes"
  ppr NameSquare     = text "NameSquare"

instance Outputable NameAnn where
  ppr (NameAnn a o n c t)
    = text "NameAnn" <+> ppr a <+> ppr o <+> ppr n <+> ppr c <+> ppr t
  ppr (NameAnnCommas a o n c t)
    = text "NameAnnCommas" <+> ppr a <+> ppr o <+> ppr n <+> ppr c <+> ppr t
  ppr (NameAnnBars a o n b t)
    = text "NameAnnBars" <+> ppr a <+> ppr o <+> ppr n <+> ppr b <+> ppr t
  ppr (NameAnnOnly a o c t)
    = text "NameAnnOnly" <+> ppr a <+> ppr o <+> ppr c <+> ppr t
  ppr (NameAnnRArrow u o n c t)
    = text "NameAnnRArrow" <+> ppr u <+> ppr o <+> ppr n <+> ppr c <+> ppr t
  ppr (NameAnnUnArrow o n c t)
    = text "NameAnnUnArrow" <+> ppr o <+> ppr n <+> ppr c <+> ppr t
  ppr (NameAnnAffArrow o n c t)
    = text "NameAnnAffArrow" <+> ppr o <+> ppr n <+> ppr c <+> ppr t
  ppr (NameAnnLinArrow o n c t)
    = text "NameAnnLinArrow" <+> ppr o <+> ppr n <+> ppr c <+> ppr t
  ppr (NameAnnQuote q n t)
    = text "NameAnnQuote" <+> ppr q <+> ppr n <+> ppr t
  ppr (NameAnnTrailing t)
    = text "NameAnnTrailing" <+> ppr t

instance Outputable AnnList where
  ppr (AnnList a o c r t)
    = text "AnnList" <+> ppr a <+> ppr o <+> ppr c <+> ppr r <+> ppr t

instance Outputable AnnPragma where
  ppr (AnnPragma o c r) = text "AnnPragma" <+> ppr o <+> ppr c <+> ppr r
