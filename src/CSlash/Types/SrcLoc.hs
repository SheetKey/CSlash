{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE TypeFamilies       #-}

module CSlash.Types.SrcLoc (
        RealSrcLoc,
        SrcLoc(..),

        mkSrcLoc, mkRealSrcLoc, mkGeneralSrcLoc,
        leftmostColumn,

        noSrcLoc, 
        generatedSrcLoc,
        interactiveSrcLoc,

        advanceSrcLoc,
        advanceBufPos,

        srcLocFile,
        srcLocLine,
        srcLocCol, 

        RealSrcSpan,
        SrcSpan(..),
        UnhelpfulSpanReason(..),

        mkGeneralSrcSpan, mkSrcSpan, mkRealSrcSpan,
        noSrcSpan, generatedSrcSpan, isGeneratedSrcSpan,
        wiredInSrcSpan,
        interactiveSrcSpan,
        srcLocSpan, realSrcLocSpan,
        combineSrcSpans,
        srcSpanFirstCharacter,

        srcSpanStart, srcSpanEnd,
        realSrcSpanStart, realSrcSpanEnd,
        srcSpanFileName_maybe,
        pprUserRealSpan, pprUnhelpfulSpanReason,
        pprUserSpan,
        unhelpfulSpanFS,
        srcSpanToRealSrcSpan,

        srcSpanFile,
        srcSpanStartLine, srcSpanEndLine,
        srcSpanStartCol, srcSpanEndCol,

        isGoodSrcSpan, isOneLineSpan, isZeroWidthSpan,
        containsSpan, isNoSrcSpan,

        isPointRealSpan,

        BufPos(..),
        getBufPos,
        BufSpan(..),
        getBufSpan,
        removeBufSpan,
        combineBufSpans,

        Located,
        RealLocated,
        GenLocated(..),

        noLoc,
        mkGeneralLocated,

        getLoc, unLoc,
        unRealSrcSpan, getRealSrcSpan,
        pprLocated,
        pprLocatedAlways,

        eqLocated, cmpLocated, cmpBufSpan,
        combineLocs, addCLoc,
        leftmost_smallest, leftmost_largest, rightmost_smallest,
        spans, isSubspanOf, isRealSubspanOf,
        sortLocated, sortRealLocated,
        lookupSrcLoc, lookupSrcSpan,

        PsLoc(..),
        PsSpan(..),
        PsLocated,
        advancePsLoc,
        mkPsSpan,
        psSpanStart,
        psSpanEnd,
        mkSrcSpanPs,
        combineRealSrcSpans,
        psLocatedToLocated,

        EpaLocation'(..), NoCommentsLocation, NoComments(..),
        DeltaPos(..), deltaPos, getDeltaLine,
    ) where

import Prelude hiding ((<>))

import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Data.FastString
import qualified CSlash.Data.Strict as Strict

import Control.DeepSeq
import Data.Data
import Data.List (sortBy, intercalate)
import Data.Function (on)
import qualified Data.Map as Map
import qualified Data.Semigroup as S
import Data.Bits (shiftR, shiftL)

data RealSrcLoc
  = SrcLoc      LexicalFastString       -- A precise location (file name)
                {-# UNPACK #-} !Int     -- line number, begins at 1
                {-# UNPACK #-} !Int     -- column number, begins at 1
  deriving (Eq, Ord)

newtype BufPos = BufPos { bufPos :: Int }
  deriving (Eq, Ord, Show, Data)

data SrcLoc
  = RealSrcLoc !RealSrcLoc !(Strict.Maybe BufPos)
  | UnhelpfulLoc !FastString
  deriving (Eq, Show)

mkSrcLoc :: FastString -> Int -> Int -> SrcLoc
mkSrcLoc x line col = RealSrcLoc (mkRealSrcLoc x line col) Strict.Nothing

mkRealSrcLoc :: FastString -> Int -> Int -> RealSrcLoc
mkRealSrcLoc x line col = SrcLoc (LexicalFastString x) line col

leftmostColumn :: Int
leftmostColumn = 1

getBufPos :: SrcLoc -> Strict.Maybe BufPos
getBufPos (RealSrcLoc _ mbpos) = mbpos
getBufPos (UnhelpfulLoc _) = Strict.Nothing

noSrcLoc, generatedSrcLoc, interactiveSrcLoc :: SrcLoc
noSrcLoc          = UnhelpfulLoc (fsLit "<no location info>")
generatedSrcLoc   = UnhelpfulLoc (fsLit "<compiler-generated code>")
interactiveSrcLoc = UnhelpfulLoc (fsLit "<interactive>")

mkGeneralSrcLoc :: FastString -> SrcLoc
mkGeneralSrcLoc = UnhelpfulLoc

srcLocFile :: RealSrcLoc -> FastString
srcLocFile (SrcLoc (LexicalFastString fname) _ _) = fname

srcLocLine :: RealSrcLoc -> Int
srcLocLine (SrcLoc _ l _) = l

srcLocCol :: RealSrcLoc -> Int
srcLocCol (SrcLoc _ _ c) = c

advanceSrcLoc :: RealSrcLoc -> Char -> RealSrcLoc
advanceSrcLoc (SrcLoc f l _) '\n' = SrcLoc f  (l + 1) 1
advanceSrcLoc (SrcLoc f l c) '\t' = SrcLoc f  l (advance_tabstop c)
advanceSrcLoc (SrcLoc f l c) _    = SrcLoc f  l (c + 1)

advance_tabstop :: Int -> Int
advance_tabstop c = ((((c - 1) `shiftR` 3) + 1) `shiftL` 3) + 1

advanceBufPos :: BufPos -> BufPos
advanceBufPos (BufPos i) = BufPos (i+1)

sortLocated :: [Located a] -> [Located a]
sortLocated = sortBy (leftmost_smallest `on` getLoc)

sortRealLocated :: [RealLocated a] -> [RealLocated a]
sortRealLocated = sortBy (compare `on` getLoc)

lookupSrcLoc :: SrcLoc -> Map.Map RealSrcLoc a -> Maybe a
lookupSrcLoc (RealSrcLoc l _) = Map.lookup l
lookupSrcLoc (UnhelpfulLoc _) = const Nothing

lookupSrcSpan :: SrcSpan -> Map.Map RealSrcSpan a -> Maybe a
lookupSrcSpan (RealSrcSpan l _) = Map.lookup l
lookupSrcSpan (UnhelpfulSpan _) = const Nothing

instance Outputable RealSrcLoc where
    ppr (SrcLoc (LexicalFastString src_path) src_line src_col)
      = hcat [ pprFastFilePath src_path <> colon
             , int src_line <> colon
             , int src_col ]

instance Outputable SrcLoc where
    ppr (RealSrcLoc l _) = ppr l
    ppr (UnhelpfulLoc s)  = ftext s

instance Data RealSrcSpan where
  toConstr _   = abstractConstr "RealSrcSpan"
  gunfold _ _  = error "gunfold"
  dataTypeOf _ = mkNoRepType "RealSrcSpan"

instance Data SrcSpan where
  toConstr _   = abstractConstr "SrcSpan"
  gunfold _ _  = error "gunfold"
  dataTypeOf _ = mkNoRepType "SrcSpan"

data RealSrcSpan
  = RealSrcSpan'
        { srcSpanFile     :: !FastString,
          srcSpanSLine    :: {-# UNPACK #-} !Int,
          srcSpanSCol     :: {-# UNPACK #-} !Int,
          srcSpanELine    :: {-# UNPACK #-} !Int,
          srcSpanECol     :: {-# UNPACK #-} !Int
        }
  deriving Eq

data BufSpan =
  BufSpan { bufSpanStart, bufSpanEnd :: {-# UNPACK #-} !BufPos }
  deriving (Eq, Ord, Show, Data)

instance Semigroup BufSpan where
  BufSpan start1 end1 <> BufSpan start2 end2 =
    BufSpan (min start1 start2) (max end1 end2)

data SrcSpan =
    RealSrcSpan !RealSrcSpan !(Strict.Maybe BufSpan)
  | UnhelpfulSpan !UnhelpfulSpanReason

  deriving (Eq, Show)

data UnhelpfulSpanReason
  = UnhelpfulNoLocationInfo
  | UnhelpfulWiredIn
  | UnhelpfulInteractive
  | UnhelpfulGenerated
  | UnhelpfulOther !FastString
  deriving (Eq, Show)

removeBufSpan :: SrcSpan -> SrcSpan
removeBufSpan (RealSrcSpan s _) = RealSrcSpan s Strict.Nothing
removeBufSpan s = s

instance NFData SrcSpan where
  rnf x = x `seq` ()

getBufSpan :: SrcSpan -> Strict.Maybe BufSpan
getBufSpan (RealSrcSpan _ mbspan) = mbspan
getBufSpan (UnhelpfulSpan _) = Strict.Nothing

noSrcSpan, generatedSrcSpan, wiredInSrcSpan, interactiveSrcSpan :: SrcSpan
noSrcSpan          = UnhelpfulSpan UnhelpfulNoLocationInfo
wiredInSrcSpan     = UnhelpfulSpan UnhelpfulWiredIn
interactiveSrcSpan = UnhelpfulSpan UnhelpfulInteractive
generatedSrcSpan   = UnhelpfulSpan UnhelpfulGenerated

isGeneratedSrcSpan :: SrcSpan -> Bool
isGeneratedSrcSpan (UnhelpfulSpan UnhelpfulGenerated) = True
isGeneratedSrcSpan _                                  = False

isNoSrcSpan :: SrcSpan -> Bool
isNoSrcSpan (UnhelpfulSpan UnhelpfulNoLocationInfo) = True
isNoSrcSpan _                                       = False

mkGeneralSrcSpan :: FastString -> SrcSpan
mkGeneralSrcSpan = UnhelpfulSpan . UnhelpfulOther

srcLocSpan :: SrcLoc -> SrcSpan
srcLocSpan (UnhelpfulLoc str) = UnhelpfulSpan (UnhelpfulOther str)
srcLocSpan (RealSrcLoc l mb) = RealSrcSpan (realSrcLocSpan l) (fmap (\b -> BufSpan b b) mb)

realSrcLocSpan :: RealSrcLoc -> RealSrcSpan
realSrcLocSpan (SrcLoc (LexicalFastString file) line col) = RealSrcSpan' file line col line col

mkRealSrcSpan :: RealSrcLoc -> RealSrcLoc -> RealSrcSpan
mkRealSrcSpan loc1 loc2 = RealSrcSpan' file line1 col1 line2 col2
  where
        line1 = srcLocLine loc1
        line2 = srcLocLine loc2
        col1 = srcLocCol loc1
        col2 = srcLocCol loc2
        file = srcLocFile loc1

isOneLineRealSpan :: RealSrcSpan -> Bool
isOneLineRealSpan (RealSrcSpan' _ line1 _ line2 _)
  = line1 == line2

isPointRealSpan :: RealSrcSpan -> Bool
isPointRealSpan (RealSrcSpan' _ line1 col1 line2 col2)
  = line1 == line2 && col1 == col2

mkSrcSpan :: SrcLoc -> SrcLoc -> SrcSpan
mkSrcSpan (UnhelpfulLoc str) _ = UnhelpfulSpan (UnhelpfulOther str)
mkSrcSpan _ (UnhelpfulLoc str) = UnhelpfulSpan (UnhelpfulOther str)
mkSrcSpan (RealSrcLoc loc1 mbpos1) (RealSrcLoc loc2 mbpos2)
    = RealSrcSpan (mkRealSrcSpan loc1 loc2) (liftA2 BufSpan mbpos1 mbpos2)

combineSrcSpans :: SrcSpan -> SrcSpan -> SrcSpan
combineSrcSpans (UnhelpfulSpan _) r = r -- this seems more useful
combineSrcSpans l (UnhelpfulSpan _) = l
combineSrcSpans (RealSrcSpan span1 mbspan1) (RealSrcSpan span2 mbspan2)
  | srcSpanFile span1 == srcSpanFile span2
      = RealSrcSpan (combineRealSrcSpans span1 span2) (liftA2 combineBufSpans mbspan1 mbspan2)
  | otherwise = UnhelpfulSpan $
      UnhelpfulOther (fsLit "<combineSrcSpans: files differ>")

combineRealSrcSpans :: RealSrcSpan -> RealSrcSpan -> RealSrcSpan
combineRealSrcSpans span1 span2
  = RealSrcSpan' file line_start col_start line_end col_end
  where
    (line_start, col_start) = min (srcSpanStartLine span1, srcSpanStartCol span1)
                                  (srcSpanStartLine span2, srcSpanStartCol span2)
    (line_end, col_end)     = max (srcSpanEndLine span1, srcSpanEndCol span1)
                                  (srcSpanEndLine span2, srcSpanEndCol span2)
    file = srcSpanFile span1

combineBufSpans :: BufSpan -> BufSpan -> BufSpan
combineBufSpans span1 span2 = BufSpan start end
  where
    start = min (bufSpanStart span1) (bufSpanStart span2)
    end   = max (bufSpanEnd   span1) (bufSpanEnd   span2)


srcSpanFirstCharacter :: SrcSpan -> SrcSpan
srcSpanFirstCharacter l@(UnhelpfulSpan {}) = l
srcSpanFirstCharacter (RealSrcSpan span mbspan) =
    RealSrcSpan (mkRealSrcSpan loc1 loc2) (fmap mkBufSpan mbspan)
  where
    loc1@(SrcLoc f l c) = realSrcSpanStart span
    loc2 = SrcLoc f l (c+1)
    mkBufSpan bspan =
      let bpos1@(BufPos i) = bufSpanStart bspan
          bpos2 = BufPos (i+1)
      in BufSpan bpos1 bpos2

isGoodSrcSpan :: SrcSpan -> Bool
isGoodSrcSpan (RealSrcSpan _ _) = True
isGoodSrcSpan (UnhelpfulSpan _) = False

isOneLineSpan :: SrcSpan -> Bool
isOneLineSpan (RealSrcSpan s _) = srcSpanStartLine s == srcSpanEndLine s
isOneLineSpan (UnhelpfulSpan _) = False

isZeroWidthSpan :: SrcSpan -> Bool
isZeroWidthSpan (RealSrcSpan s _) = srcSpanStartLine s == srcSpanEndLine s
                                 && srcSpanStartCol s == srcSpanEndCol s
isZeroWidthSpan (UnhelpfulSpan _) = False

containsSpan :: RealSrcSpan -> RealSrcSpan -> Bool
containsSpan s1 s2
  = (srcSpanStartLine s1, srcSpanStartCol s1)
       <= (srcSpanStartLine s2, srcSpanStartCol s2)
    && (srcSpanEndLine s1, srcSpanEndCol s1)
       >= (srcSpanEndLine s2, srcSpanEndCol s2)
    && (srcSpanFile s1 == srcSpanFile s2)

srcSpanStartLine :: RealSrcSpan -> Int
srcSpanEndLine :: RealSrcSpan -> Int
srcSpanStartCol :: RealSrcSpan -> Int
srcSpanEndCol :: RealSrcSpan -> Int

srcSpanStartLine RealSrcSpan'{ srcSpanSLine=l } = l
srcSpanEndLine RealSrcSpan'{ srcSpanELine=l } = l
srcSpanStartCol RealSrcSpan'{ srcSpanSCol=l } = l
srcSpanEndCol RealSrcSpan'{ srcSpanECol=c } = c

srcSpanStart :: SrcSpan -> SrcLoc
srcSpanStart (UnhelpfulSpan r) = UnhelpfulLoc (unhelpfulSpanFS r)
srcSpanStart (RealSrcSpan s b) = RealSrcLoc (realSrcSpanStart s) (fmap bufSpanStart b)

srcSpanEnd :: SrcSpan -> SrcLoc
srcSpanEnd (UnhelpfulSpan r) = UnhelpfulLoc (unhelpfulSpanFS r)
srcSpanEnd (RealSrcSpan s b) = RealSrcLoc (realSrcSpanEnd s) (fmap bufSpanEnd b)

realSrcSpanStart :: RealSrcSpan -> RealSrcLoc
realSrcSpanStart s = mkRealSrcLoc (srcSpanFile s)
                                  (srcSpanStartLine s)
                                  (srcSpanStartCol s)

realSrcSpanEnd :: RealSrcSpan -> RealSrcLoc
realSrcSpanEnd s = mkRealSrcLoc (srcSpanFile s)
                                (srcSpanEndLine s)
                                (srcSpanEndCol s)

srcSpanFileName_maybe :: SrcSpan -> Maybe FastString
srcSpanFileName_maybe (RealSrcSpan s _) = Just (srcSpanFile s)
srcSpanFileName_maybe (UnhelpfulSpan _) = Nothing

srcSpanToRealSrcSpan :: SrcSpan -> Maybe RealSrcSpan
srcSpanToRealSrcSpan (RealSrcSpan ss _) = Just ss
srcSpanToRealSrcSpan _ = Nothing

instance Ord RealSrcSpan where
  compare = on compare realSrcSpanStart S.<> on compare realSrcSpanEnd

instance Show RealSrcLoc where
  show (SrcLoc filename row col)
      = "SrcLoc " ++ show filename ++ " " ++ show row ++ " " ++ show col

instance Show RealSrcSpan where
  show span@(RealSrcSpan' file sl sc el ec)
    | isPointRealSpan span
    = "SrcSpanPoint " ++ show file ++ " " ++ intercalate " " (map show [sl,sc])

    | isOneLineRealSpan span
    = "SrcSpanOneLine " ++ show file ++ " "
                        ++ intercalate " " (map show [sl,sc,ec])

    | otherwise
    = "SrcSpanMultiLine " ++ show file ++ " "
                          ++ intercalate " " (map show [sl,sc,el,ec])


instance Outputable RealSrcSpan where
    ppr span = pprUserRealSpan True span

instance Outputable SrcSpan where
    ppr span = pprUserSpan True span

instance Outputable UnhelpfulSpanReason where
    ppr = pprUnhelpfulSpanReason

unhelpfulSpanFS :: UnhelpfulSpanReason -> FastString
unhelpfulSpanFS r = case r of
  UnhelpfulOther s        -> s
  UnhelpfulNoLocationInfo -> fsLit "<no location info>"
  UnhelpfulWiredIn        -> fsLit "<wired into compiler>"
  UnhelpfulInteractive    -> fsLit "<interactive>"
  UnhelpfulGenerated      -> fsLit "<generated>"

pprUnhelpfulSpanReason :: UnhelpfulSpanReason -> SDoc
pprUnhelpfulSpanReason r = ftext (unhelpfulSpanFS r)

pprUserSpan :: Bool -> SrcSpan -> SDoc
pprUserSpan _         (UnhelpfulSpan r) = pprUnhelpfulSpanReason r
pprUserSpan show_path (RealSrcSpan s _) = pprUserRealSpan show_path s

pprUserRealSpan :: Bool -> RealSrcSpan -> SDoc
pprUserRealSpan show_path span@(RealSrcSpan' src_path line col _ _)
  | isPointRealSpan span
  = hcat [ ppWhen show_path (pprFastFilePath src_path <> colon)
         , int line <> colon
         , int col ]

pprUserRealSpan show_path span@(RealSrcSpan' src_path line scol _ ecol)
  | isOneLineRealSpan span
  = hcat [ ppWhen show_path (pprFastFilePath src_path <> colon)
         , int line <> colon
         , int scol
         , ppUnless (ecol - scol <= 1) (char '-' <> int (ecol - 1)) ]

pprUserRealSpan show_path (RealSrcSpan' src_path sline scol eline ecol)
  = hcat [ ppWhen show_path (pprFastFilePath src_path <> colon)
         , parens (int sline <> comma <> int scol)
         , char '-'
         , parens (int eline <> comma <> int ecol') ]
 where
   ecol' = if ecol == 0 then ecol else ecol - 1

data GenLocated l e = L l e
  deriving (Eq, Ord, Show, Data, Functor, Foldable, Traversable)
instance (NFData l, NFData e) => NFData (GenLocated l e) where
  rnf (L l e) = rnf l `seq` rnf e

type Located = GenLocated SrcSpan
type RealLocated = GenLocated RealSrcSpan

unLoc :: GenLocated l e -> e
unLoc (L _ e) = e

getLoc :: GenLocated l e -> l
getLoc (L l _) = l

noLoc :: e -> Located e
noLoc e = L noSrcSpan e

mkGeneralLocated :: String -> e -> Located e
mkGeneralLocated s e = L (mkGeneralSrcSpan (fsLit s)) e

combineLocs :: Located a -> Located b -> SrcSpan
combineLocs a b = combineSrcSpans (getLoc a) (getLoc b)

addCLoc :: Located a -> Located b -> c -> Located c
addCLoc a b c = L (combineSrcSpans (getLoc a) (getLoc b)) c

eqLocated :: Eq a => GenLocated l a -> GenLocated l a -> Bool
eqLocated a b = unLoc a == unLoc b

cmpLocated :: Ord a => GenLocated l a -> GenLocated l a -> Ordering
cmpLocated a b = unLoc a `compare` unLoc b

cmpBufSpan :: HasDebugCallStack => Located a -> Located a -> Ordering
cmpBufSpan (L l1 _) (L l2  _)
  | Strict.Just a <- getBufSpan l1
  , Strict.Just b <- getBufSpan l2
  = compare a b

  | otherwise = panic "cmpBufSpan: no BufSpan"

instance (Outputable e) => Outputable (Located e) where
  ppr (L l e) =
                whenPprDebug (braces (pprUserSpan False l))
             $$ ppr e
instance (Outputable e) => Outputable (GenLocated RealSrcSpan e) where
  ppr (L l e) =
                whenPprDebug (braces (pprUserSpan False (RealSrcSpan l Strict.Nothing)))
             $$ ppr e


pprLocated :: (Outputable l, Outputable e) => GenLocated l e -> SDoc
pprLocated (L l e) =
                whenPprDebug (braces (ppr l))
             $$ ppr e

pprLocatedAlways :: (Outputable l, Outputable e) => GenLocated l e -> SDoc
pprLocatedAlways (L l e) =
     braces (ppr l)
  $$ ppr e

leftmost_smallest, leftmost_largest, rightmost_smallest :: SrcSpan -> SrcSpan -> Ordering
rightmost_smallest = compareSrcSpanBy (flip compare)
leftmost_smallest = compareSrcSpanBy compare
leftmost_largest = compareSrcSpanBy $
  on compare realSrcSpanStart S.<> flip (on compare realSrcSpanEnd)

compareSrcSpanBy :: (RealSrcSpan -> RealSrcSpan -> Ordering) -> SrcSpan -> SrcSpan -> Ordering
compareSrcSpanBy cmp (RealSrcSpan a _) (RealSrcSpan b _) = cmp a b
compareSrcSpanBy _   (RealSrcSpan _ _) (UnhelpfulSpan _) = LT
compareSrcSpanBy _   (UnhelpfulSpan _) (RealSrcSpan _ _) = GT
compareSrcSpanBy _   (UnhelpfulSpan _) (UnhelpfulSpan _) = EQ

spans :: SrcSpan -> (Int, Int) -> Bool
spans (UnhelpfulSpan _) _ = panic "spans UnhelpfulSpan"
spans (RealSrcSpan span _) (l,c) = realSrcSpanStart span <= loc && loc <= realSrcSpanEnd span
   where loc = mkRealSrcLoc (srcSpanFile span) l c

isSubspanOf :: SrcSpan -- ^ The span that may be enclosed by the other
            -> SrcSpan -- ^ The span it may be enclosed by
            -> Bool
isSubspanOf (RealSrcSpan src _) (RealSrcSpan parent _) = isRealSubspanOf src parent
isSubspanOf _ _ = False

isRealSubspanOf :: RealSrcSpan -- ^ The span that may be enclosed by the other
                -> RealSrcSpan -- ^ The span it may be enclosed by
                -> Bool
isRealSubspanOf src parent
    | srcSpanFile parent /= srcSpanFile src = False
    | otherwise = realSrcSpanStart parent <= realSrcSpanStart src &&
                  realSrcSpanEnd parent   >= realSrcSpanEnd src

getRealSrcSpan :: RealLocated a -> RealSrcSpan
getRealSrcSpan (L l _) = l

unRealSrcSpan :: RealLocated a -> a
unRealSrcSpan  (L _ e) = e

data PsLoc
  = PsLoc { psRealLoc :: !RealSrcLoc, psBufPos :: !BufPos }
  deriving (Eq, Ord, Show)

data PsSpan
  = PsSpan { psRealSpan :: !RealSrcSpan, psBufSpan :: !BufSpan }
  deriving (Eq, Ord, Show, Data)

type PsLocated = GenLocated PsSpan

psLocatedToLocated :: PsLocated a -> Located a
psLocatedToLocated (L sp a) = L (mkSrcSpanPs sp) a

advancePsLoc :: PsLoc -> Char -> PsLoc
advancePsLoc (PsLoc real_loc buf_loc) c =
  PsLoc (advanceSrcLoc real_loc c) (advanceBufPos buf_loc)

mkPsSpan :: PsLoc -> PsLoc -> PsSpan
mkPsSpan (PsLoc r1 b1) (PsLoc r2 b2) = PsSpan (mkRealSrcSpan r1 r2) (BufSpan b1 b2)

psSpanStart :: PsSpan -> PsLoc
psSpanStart (PsSpan r b) = PsLoc (realSrcSpanStart r) (bufSpanStart b)

psSpanEnd :: PsSpan -> PsLoc
psSpanEnd (PsSpan r b) = PsLoc (realSrcSpanEnd r) (bufSpanEnd b)

mkSrcSpanPs :: PsSpan -> SrcSpan
mkSrcSpanPs (PsSpan r b) = RealSrcSpan r (Strict.Just b)

data EpaLocation' a = EpaSpan !SrcSpan
                    | EpaDelta !DeltaPos !a
                    deriving (Data,Eq,Show)

type NoCommentsLocation = EpaLocation' NoComments

data NoComments = NoComments
  deriving (Data,Eq,Ord,Show)

data DeltaPos
  = SameLine { deltaColumn :: !Int }
  | DifferentLine
      { deltaLine   :: !Int, -- deltaLine should always be > 0
        deltaColumn :: !Int
      } deriving (Show,Eq,Ord,Data)

deltaPos :: Int -> Int -> DeltaPos
deltaPos l c = case l of
  0 -> SameLine c
  _ -> DifferentLine l c

getDeltaLine :: DeltaPos -> Int
getDeltaLine (SameLine _) = 0
getDeltaLine (DifferentLine r _) = r

instance Outputable NoComments where
  ppr NoComments = text "NoComments"

instance (Outputable a) => Outputable (EpaLocation' a) where
  ppr (EpaSpan r) = text "EpaSpan" <+> ppr r
  ppr (EpaDelta d cs) = text "EpaDelta" <+> ppr d <+> ppr cs

instance Outputable DeltaPos where
  ppr (SameLine c) = text "SameLine" <+> ppr c
  ppr (DifferentLine l c) = text "DifferentLine" <+> ppr l <+> ppr c
