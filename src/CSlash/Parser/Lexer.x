{
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnboxedSums #-}
{-# LANGUAGE UnliftedNewtypes #-}
{-# LANGUAGE PatternSynonyms #-}

{-# OPTIONS_GHC -funbox-strict-fields #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module CSlash.Parser.Lexer where

import qualified CSlash.Data.Strict as Strict

-- base
import Data.Char
import Data.List (stripPrefix, isInfixOf, partition)
import Data.Word
import Debug.Trace (trace)

import Control.Monad
import Control.Applicative

-- compiler
import CSlash.Data.StringBuffer
import CSlash.Data.FastString
import CSlash.Data.EnumSet as EnumSet
import CSlash.Data.Maybe

import CSlash.Driver.Flags

import CSlash.Parser.Annotation
import CSlash.Parser.CharClass
import CSlash.Parser.Errors.Basic
import CSlash.Parser.Errors.Ppr
import CSlash.Parser.Errors.Types

import CSlash.Types.Error
import CSlash.Types.SourceText
import CSlash.Types.SrcLoc
import CSlash.Types.Unique.FM

import CSlash.Utils.Error
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
  
}

-- As in GHC
%encoding "utf8" 

-- -----------------------------------------------------------------------------
-- Alex "Character set macros"

$unispace = \x05
$nl = [\n\r\f]
$whitechar = [$nl\v\ $unispace]
$white_no_nl = $whitechar # \n
$tab = \t

$ascdigit = 0-9
$decdigit = $ascdigit
$digit = [$ascdigit]

$special = [\(\)\,\;\[\]\`\{\}]
$ascsymbol = [\!\#\$\%\&\*\+\.\/\<\=\>\?\@\\\^\|\-\~\:]
$unisymbol = \x04
$symbol = [$ascsymbol $unisymbol] # [$special \_\"\']

$unilarge = \x01
$asclarge = [A-Z]
$large = [$asclarge $unilarge]

$unismall = \x02
$ascsmall = [a-z]
$small = [$ascsmall $unismall \_]

$uniidchar = \x07
$idchar = [$small $large $digit $uniidchar \']

$unigraphic = \x06
$graphic = [$small $large $symbol $digit $idchar $special $unigraphic \"\']

$binit = 0-1
$octit = 0-7
$hexit = [$decdigit A-F a-f]

$docsym = [\| \^ \* \$]

-- -----------------------------------------------------------------------------
-- Alex "Regular expression macros"

@varid = $small $idchar*
@conid = $large $idchar*

@varsym = ($symbol # \:) $symbol*
@consym = \: $symbol+

@numspc = _*
@decimal = $decdigit(@numspc $decdigit)*
@binary = $binit(@numspc $binit)*
@octal = $octit(@numspc $octit)*
@hexadecimal = $hexit(@numspc $hexit)*
@exponent = @numspc [eE] [\-\+]? @decimal
@bin_exponent = @numspc [pP] [\-\+]? @decimal

@binarylit = 0[bB] @numspc @binary
@octallit = 0[oO] @numspc @octal
@hexadecimallit = 0[xX] @numspc @hexadecimal

@qual = (@conid \.)+
@qvarid = @qual @varid
@qconid = @qual @conid
@qvarsym = @qual @varsym
@qconsym = @qual @consym

@floating_point = @numspc @decimal \. @decimal @exponent? | @numspc @decimal @exponent
@hex_floating_point = @numspc @hexadecimal \. @hexadecimal @bin_exponent? | @numspc @hexadecimal @bin_exponent

@negative = \-

-- -----------------------------------------------------------------------------
-- Alex "Identifier"

cslash :-

-- -----------------------------------------------------------------------------
-- Alex "Rules"

$white_no_nl+ ;
$tab { warnTab }

"{-" / { isNormalComment } { nested_comment }

"-- " ~$docsym .* { lineCommentToken }
"--" [^$symbol \ ] .* { lineCommentToken }

"-- " $docsym .* { lineCommentToken }

"---"\-* ~$symbol .* { lineCommentToken }

"--"\-* / { atEOL } { lineCommentToken }

"-- " / { atEOL } { lineCommentToken }

$unigraphic / { isSmartQuote } { smart_quote_error }

<bol> {
  \n ;
  () { do_bol }
}

-- layout keywords are let, where, do, of (as in case ... of ...)
<layout, layout_if> \n ;

<layout_if> {
  \| / { notFollowedBySymbol } { new_layout_context dontGenerateSemic ITvbar }
  () { pop }
}

<layout> () { new_layout_context generateSemic ITolayout }

<layout_left> () { do_layout_left }

<0> \n { begin bol }

-- "special" symbols

<0> {
  \( { special IToparen }
  \) { special ITcparen }
  \, { special ITcomma }
  \` { special ITbackquote }
  \{ { special ITocurly }
  \} { special ITccurly }
}

<0> {
  @qvarid { idtoken qvarid }
  @qconid { idtoken qconid }
  @varid { varid }
  @conid { idtoken conid }
}

<0> {
  @qvarsym { idtoken qvarsym }
  @qconsym { idtoken qconsym }
  @varsym { with_op_ws varsym }
  @consym { with_op_ws consym }
}

<0> {
  @decimal { tok_num positive 0 0 decimal }
  @binarylit { tok_num positive 2 2 binary }
  @octallit { tok_num positive 2 2 octal }
  @hexadecimallit { tok_num positive 2 2 hexadecimal }
  @negative @decimal / { negLitPred } { tok_num negative 1 1 decimal }
  @negative @binarylit / { negLitPred } { tok_num negative 3 3 binary }
  @negative @octallit / { negLitPred } { tok_num negative 3 3 octal }
  @negative @hexadecimallit / { negLitPred } { tok_num negative 3 3 hexadecimal }
  
  @floating_point { tok_frac 0 tok_float }
  @negative @floating_point / { negLitPred } { tok_frac 0 tok_float }
  0[xX] @numspc @hex_floating_point { tok_frac 0 tok_hex_float }
  @negative 0[xX] @numspc @hex_floating_point / { negLitPred }
                                                { tok_frac 0 tok_hex_float }
}

<0> {
  \' { lex_char_tok }
  \" { lex_string_tok }
}

-- -----------------------------------------------------------------------------
-- Alex "Haskell code fragment bottom"

{

-- Operator whitespace occurrence.
data OpWs
  = OpWsPrefix         -- a !b
  | OpWsSuffix         -- a! b
  | OpWsTightInfix     -- a!b
  | OpWsLooseInfix     -- a ! b
  deriving Show

-- -----------------------------------------------------------------------------
-- The token type

data Token
  = ITas
  | ITcase
  | ITelse
  | IThiding
  | ITif
  | ITimport
  | ITin
  | ITinfix
  | ITinfixl
  | ITinfixr
  | ITlet
  | ITmodule
  | ITof
  | ITqualified
  | ITthen
  | ITtype
  | ITwhere

  | ITforall

  | ITcolon
  | ITequal
  | ITlam
  | ITdlam
  | ITvbar
  | ITlarrow
  | ITrarrow
  | ITdarrow
  | ITarrowU
  | ITarrowA
  | ITarrowL
  | ITprefixminus
  | ITsuffixarr
  | ITtightinfixat
  | ITstar
  | ITbullet
  | ITcirc
  | ITdot

  | ITbiglam

  | ITolayout -- In GHC these are ITvocurly, ITvccurly, ITsemi
  | ITclayout
  | ITnewlinelayout

  | ITocurly
  | ITccurly
  | IToparen
  | ITcparen
  | ITcomma
  | ITunderscore
  | ITbackquote

  | ITvarid FastString
  | ITconid FastString
  | ITvarsym FastString
  | ITconsym FastString
  | ITqvarid (FastString, FastString)
  | ITqconid (FastString, FastString)
  | ITqvarsym (FastString, FastString)
  | ITqconsym (FastString, FastString)

  | ITchar SourceText Char
  | ITstring SourceText FastString
  | ITinteger IntegralLit
  | ITrational FractionalLit

  | ITunknown String
  | ITeof

  | ITlineComment String PsSpan
  | ITblockComment String PsSpan

  deriving (Show)

instance Outputable Token where
  ppr x = text (show x)

reservedWordsFM :: UniqFM FastString Token
reservedWordsFM = listToUFM $
  map (\ (x, y) -> (mkFastString x, y))
      [ ("_", ITunderscore)
      , ("as", ITas)
      , ("case", ITcase)
      , ("else", ITelse)
      , ("hiding", IThiding)
      , ("if", ITif)
      , ("import", ITimport)
      , ("in", ITin)
      , ("infix", ITinfix)
      , ("infixl", ITinfixl)
      , ("infixr", ITinfixr)
      , ("let", ITlet)
      , ("module", ITmodule)
      , ("of", ITof)
      , ("qualified", ITqualified)
      , ("then", ITthen)
      , ("type", ITtype)
      , ("where", ITwhere)
      ]

reservedSymsFM :: UniqFM FastString (Token, IsUnicodeSyntax)
reservedSymsFM = listToUFM $
  map (\ (x, y, z) -> (mkFastString x, (y, z)))
      [ (":", ITcolon, NormalSyntax)
      , ("=", ITequal, NormalSyntax)
      , ("\\", ITlam, NormalSyntax)
      , ("\\\\", ITdlam, NormalSyntax)
      , ("/\\", ITbiglam, NormalSyntax)
      , ("|", ITvbar, NormalSyntax)
      , ("<-", ITlarrow, NormalSyntax)
      , ("->", ITrarrow, NormalSyntax)
      , ("=>", ITdarrow, NormalSyntax)
      , ("-★>", ITarrowU, UnicodeSyntax)
      , ("-●>", ITarrowA, UnicodeSyntax)
      , ("-○>", ITarrowL, UnicodeSyntax)

      , ("★", ITstar, UnicodeSyntax)
      , ("●", ITbullet, UnicodeSyntax)
      , ("○", ITcirc, UnicodeSyntax)

      , ("∀", ITforall, UnicodeSyntax)
      ]

-- -----------------------------------------------------------------------------
-- Lexer actions

type Action = PsSpan -> StringBuffer -> Int -> StringBuffer -> P (PsLocated Token)

special :: Token -> Action
special tok span _buf _len _buf2 = return (L span tok)

token :: Token -> Action
token tok span _buf _len _buf2 = return (L span tok)

layout_token :: Token -> Action
layout_token tok span _buf _len _buf2 = pushLexState layout >> return (L span tok)

idtoken :: (StringBuffer -> Int -> Token) -> Action
idtoken f span buf len _buf2 = return (L span $! (f buf len))

skip_one_varid :: (FastString -> Token) -> Action
skip_one_varid f span buf len _buf2
  = return (L span $! f (lexemeToFastString (stepOn buf) (len-1)))

skip_one_varid_src :: (SourceText -> FastString -> Token) -> Action
skip_one_varid_src f span buf len _buf2
  = return (L span $! f (SourceText $ lexemeToFastString (stepOn buf) (len-1))
                        (lexemeToFastString (stepOn buf) (len-1)))

skip_two_varid :: (FastString -> Token) -> Action
skip_two_varid f span buf len _buf2
  = return (L span $! f (lexemeToFastString (stepOn (stepOn buf)) (len-2)))

strtoken :: (String -> Token) -> Action
strtoken f span buf len _buf2 =
  return (L span $! (f $! lexemeToString buf len))

fstrtoken :: (FastString -> Token) -> Action
fstrtoken f span buf len _buf2 =
  return (L span $! (f $! lexemeToFastString buf len))

begin :: Int -> Action
begin code _span _str _len _buf2 = do pushLexState code; lexToken

pop :: Action
pop _span _buf _len _buf2 = do
  _ <- popLexState
  lexToken

pop_and :: Action -> Action
pop_and act span buf len buf2 = do
  _ <- popLexState
  act span buf len buf2

followedByOpeningToken :: AlexAccPred ExtsBitmap
followedByOpeningToken _ _ _ (AI _ buf) = followedByOpeningToken' buf

precededByClosingToken :: AlexAccPred ExtsBitmap
precededByClosingToken _ (AI _ buf) _ _ = precededByClosingToken' buf

followedByOpeningToken' :: StringBuffer -> Bool
followedByOpeningToken' buf
  | atEnd buf = False
  | otherwise =
      case nextChar buf of
        ('(', _) -> True
        ('\"', _) -> True
        ('\'', _) -> True
        ('_', _) -> True
        (c, _) -> isAlphaNum c

precededByClosingToken' :: StringBuffer -> Bool
precededByClosingToken' buf =
  case prevChar buf '\n' of
    ')' -> True
    '\"' -> True
    '\'' -> True
    '_' -> True
    c -> isAlphaNum c

get_op_ws :: StringBuffer -> StringBuffer -> OpWs
get_op_ws buf1 buf2 =
    mk_op_ws (precededByClosingToken' buf1) (followedByOpeningToken' buf2)
  where
    mk_op_ws False True = OpWsPrefix
    mk_op_ws True False = OpWsSuffix
    mk_op_ws True True = OpWsTightInfix
    mk_op_ws False False = OpWsLooseInfix

{-# INLINE with_op_ws #-}
with_op_ws :: (OpWs -> Action) -> Action
with_op_ws act span buf len buf2 = act (get_op_ws buf buf2) span buf len buf2

{-# INLINE nextCharIs #-}
nextCharIs :: StringBuffer -> (Char -> Bool) -> Bool
nextCharIs buf p = not (atEnd buf) && p (currentChar buf)

{-# INLINE nextCharIsNot #-}
nextCharIsNot :: StringBuffer -> (Char -> Bool) -> Bool
nextCharIsNot buf p = not (nextCharIs buf p)

notFollowedBy :: Char -> AlexAccPred ExtsBitmap
notFollowedBy char _ _ _ (AI _ buf)
  = nextCharIsNot buf (== char)

notFollowedBySymbol :: AlexAccPred ExtsBitmap
notFollowedBySymbol _ _ _ (AI _ buf)
  = nextCharIsNot buf (`elem` "!#$%&*+./<=>?@\\^|-~")

followedByDigit :: AlexAccPred ExtsBitmap
followedByDigit _ _ _ (AI _ buf)
  = afterOptionalSpace buf (\ b -> nextCharIs b (`elem` ['0'..'9']))

ifCurrentChar :: Char -> AlexAccPred ExtsBitmap
ifCurrentChar char _ (AI _ buf) _ _
  = nextCharIs buf (== char)

isNormalComment :: AlexAccPred ExtsBitmap
isNormalComment bits _ _ (AI _ buf) = nextCharIsNot buf (== '#')

afterOptionalSpace :: StringBuffer -> (StringBuffer -> Bool) -> Bool
afterOptionalSpace buf p
  = if nextCharIs buf (== ' ')
    then p (snd (nextChar buf))
    else p buf

atEOL :: AlexAccPred ExtsBitmap
atEOL _ _ _ (AI _ buf) = atEnd buf || currentChar buf == '\n'

-- We parse '-' as if GHC LexicalNegation is on by default.
negLitPred :: AlexAccPred ExtsBitmap
negLitPred = alexNotPred precededByClosingToken

alexNotPred p userState in1 len in2
  = not (p userState in1 len in2)

lineCommentToken :: Action
lineCommentToken span buf len buf2 = do
  b <- isRawTokenStream
  if b then do
         lt <- getLastLocIncludingComments
         strtoken (\s -> ITlineComment s lt) span buf len buf2
       else lexToken

nested_comment :: Action
nested_comment span buf len _buf2 = do
  l <- getLastLocIncludingComments
  let endComment input (L _ comment)
        = commentEnd lexToken input (ITblockComment comment l) buf span
  input <- getInput
  let start_decorator = reverse $ lexemeToString buf len
  nested_comment_logic endComment start_decorator input span

{-# INLINE nested_comment_logic #-}
nested_comment_logic
  :: (AlexInput -> Located String -> P (PsLocated Token))
  -> String
  -> AlexInput
  -> PsSpan
  -> P (PsLocated Token)
nested_comment_logic endComment commentAcc input span = go commentAcc (1::Int) input
  where
    go commentAcc 0 input@(AI end_loc _) = do
      let comment = reverse commentAcc
          cspan = mkSrcSpanPs $ mkPsSpan (psSpanStart span) end_loc
          lcomment = L cspan comment
      endComment input lcomment
    go commentAcc n input = case alexGetChar' input of
      Nothing -> errBrace input (psRealSpan span)
      Just ('-', input) -> case alexGetChar' input of
        Nothing -> errBrace input (psRealSpan span)
        Just ('\125', input) -> go ('\125' : '-' : commentAcc) (n-1) input
        Just (_, _) -> go ('-' : commentAcc) n input
      Just ('\123', input) -> case alexGetChar' input of
        Nothing -> errBrace input (psRealSpan span)
        Just ('-', input) -> go ('-' : '\123' : commentAcc) (n+1) input
        Just (_, _) -> go ('\123' : commentAcc) n input
      Just ('\n', input) -> case alexGetChar' input of
        Nothing -> errBrace input (psRealSpan span)
        Just (_, _) -> go ('\n' : commentAcc) n input
      Just (c, input) -> go (c : commentAcc) n input

{-# INLINE commentEnd #-}
commentEnd
  :: P (PsLocated Token)
  -> AlexInput
  -> Token
  -> StringBuffer
  -> PsSpan
  -> P (PsLocated Token)
commentEnd cont input token buf span = do
  setInput input
  let (AI loc nextBuf) = input
      span' = mkPsSpan (psSpanStart span) loc
      last_len = byteDiff buf nextBuf
  span `seq` setLastToken span' last_len
  b <- isRawTokenStream
  if b then return (L span' token)
       else cont

errBrace :: AlexInput -> RealSrcSpan -> P a
errBrace (AI end _) span =
  failLocMsgP (realSrcSpanStart span)
              (psRealLoc end)
              (\ srcLoc -> mkPlainErrorMsgEnvelope
                             srcLoc
                             (PsErrLexer LexUnterminatedComment LexErrKind_EOF))

qvarid :: StringBuffer -> Int -> Token
qvarid buf len = ITqvarid $! splitQualName buf len False

qconid :: StringBuffer -> Int -> Token
qconid buf len = ITqconid $! splitQualName buf len False

splitQualName :: StringBuffer -> Int -> Bool -> (FastString, FastString)
splitQualName orig_buf len parens = split orig_buf orig_buf
  where
    split buf dot_buf
        | orig_buf `byteDiff` buf >= len = done dot_buf
        | c == '.'                       = found_dot buf'
        | otherwise                      = split buf' dot_buf
      where
        (c, buf') = nextChar buf
    found_dot buf
        | isUpper c = split buf' buf
        | otherwise = done buf
      where
        (c, buf') = nextChar buf
    done dot_buf
        | qual_size < 1 = error "splitQualName got an unqualified name"
        | otherwise =
        ( lexemeToFastString orig_buf (qual_size - 1)
        , if parens
             then lexemeToFastString (stepOn dot_buf) (len - qual_size - 2)
             else lexemeToFastString dot_buf (len - qual_size)
        )
      where
        qual_size = orig_buf `byteDiff` dot_buf

varid :: Action
varid span buf len _buf2 =
  case lookupUFM reservedWordsFM fs of
    Just keyword -> do
      maybe_layout keyword
      return $ L span keyword
    Nothing -> return $ L span $ ITvarid fs
  where
    !fs = lexemeToFastString buf len

conid :: StringBuffer -> Int -> Token
conid buf len = ITconid $! lexemeToFastString buf len

qvarsym :: StringBuffer -> Int -> Token
qvarsym buf len = ITqvarsym $! splitQualName buf len False

qconsym :: StringBuffer -> Int -> Token
qconsym buf len = ITqconsym $! splitQualName buf len False

varsym :: OpWs -> Action
varsym opws@OpWsPrefix = sym $ \ span s ->
  if | s == fsLit "-" -> return ITprefixminus
     | s == fsLit "." -> return ITdot
     | otherwise -> do
         warnOperatorWhitespace opws span s
         return (ITvarsym s)
varsym opws@OpWsSuffix = sym $ \ span s ->
  if | s == fsLit "." -> return ITdot
     | s == fsLit ">" -> return ITsuffixarr
     | otherwise -> do
        warnOperatorWhitespace opws span s
        return (ITvarsym s)
varsym opws@OpWsTightInfix = sym $ \ span s ->
  if | s == fsLit "@" -> return ITtightinfixat
     | s == fsLit "." -> return ITdot
     | otherwise -> do warnOperatorWhitespace opws span s
                       return (ITvarsym s)
varsym OpWsLooseInfix = sym $ \ _ s ->
  if | s == fsLit "." -> return ITdot
     | otherwise -> return (ITvarsym s)

consym :: OpWs -> Action
consym opws = sym $ \ span s -> do
  warnOperatorWhitespace opws span s
  return (ITconsym s)

warnOperatorWhitespace :: OpWs -> PsSpan -> FastString -> P ()
warnOperatorWhitespace opws span s =
  whenIsJust (check_unusual_opws opws) $ \ opws' ->
    addPsMessage
      (mkSrcSpanPs span)
      (PsWarnOperatorWhitespace s opws')

check_unusual_opws :: OpWs -> Maybe OperatorWhitespaceOccurrence
check_unusual_opws opws =
  case opws of
    OpWsPrefix -> Just OperatorWhitespaceOccurrence_Prefix
    OpWsSuffix -> Just OperatorWhitespaceOccurrence_Suffix
    OpWsTightInfix -> Just OperatorWhitespaceOccurrence_TightInfix
    OpWsLooseInfix -> Nothing

sym :: (PsSpan -> FastString -> P Token) -> Action
sym con span buf len _buf2 =
  case lookupUFM reservedSymsFM fs of
    Just (keyword, NormalSyntax) ->
      return $ L span keyword
    Just (keyword, UnicodeSyntax) -> 
      return $ L span keyword
    Nothing ->
      L span <$!> con span fs
  where
    !fs = lexemeToFastString buf len

tok_integral
  :: (SourceText -> Integer -> Token)
  -> (Integer -> Integer)
  -> Int -> Int
  -> (Integer, (Char -> Int))
  -> Action
tok_integral itint transint transbuf translen (radix, char_to_int) span buf len _buf2 =
  let src = lexemeToFastString buf len
  in return $ L span $ itint (SourceText src)
      $! transint $ parseUnsignedInteger
      (offsetBytes transbuf buf) (subtract translen len) radix char_to_int

tok_num
  :: (Integer -> Integer)
  -> Int -> Int
  -> (Integer, (Char -> Int))
  -> Action
tok_num = tok_integral $ \case
    st@(SourceText (unconsFS -> Just ('-', _))) -> itint st (const True)
    st@(SourceText _) -> itint st (const False)
    st@NoSourceText -> itint st (< 0)
  where
    itint :: SourceText -> (Integer -> Bool) -> Integer -> Token
    itint !st is_negative !val = ITinteger ((IL st $! is_negative val) val)

positive :: Integer -> Integer
positive = id

negative :: Integer -> Integer
negative = negate

decimal :: (Integer, Char -> Int)
decimal = (10, octDecDigit)

binary :: (Integer, Char -> Int)
binary = (2, octDecDigit)

octal :: (Integer, Char -> Int)
octal = (8, octDecDigit)

hexadecimal :: (Integer, Char -> Int)
hexadecimal = (16, hexDigit)

tok_frac :: Int -> (String -> Token) -> Action
tok_frac drop f span buf len _buf2 = 
  let src = lexemeToString buf (len-drop)
  in return (L span $! (f $! src))

tok_float :: String -> Token
tok_float str = ITrational $! readFractionalLit str

tok_hex_float :: String -> Token
tok_hex_float str = ITrational $! readHexFractionalLit str

readFractionalLit :: String -> FractionalLit
readFractionalLit = readFractionalLitX readSignificandExponentPair Base10

readHexFractionalLit :: String -> FractionalLit
readHexFractionalLit = readFractionalLitX readHexSignificandExponentPair Base2

readFractionalLitX
  :: (String -> (Integer, Integer))
  -> FractionalExponentBase
  -> String
  -> FractionalLit
readFractionalLitX readStr b str =
  mkSourceFractionalLit str is_neg i e b
  where
    is_neg = case str of
                 '-' : _ -> True
                 _       -> False
    (i, e) = readStr str

-- -----------------------------------------------------------------------------
-- Layout processing

do_bol :: Action
do_bol span _str _len _buf2 = do
  (pos, gen_semic) <- getOffside
  case pos of
      LT -> do
          popContext
          return (L span ITclayout)
      EQ | gen_semic -> do
          _ <- popLexState
          return (L span ITnewlinelayout)
      _ -> do
          _ <- popLexState
          lexToken

maybe_layout :: Token -> P ()
maybe_layout t = f t
  where
    f ITof = pushLexState layout
    f ITlet = pushLexState layout
    f ITif = pushLexState layout_if
    f ITwhere = pushLexState layout
    -- f ITtype = pushLexState layout
    f _ = return ()

new_layout_context :: Bool -> Token -> Action
new_layout_context gen_semic tok span _buf len _buf2 = do
  _ <- popLexState
  (AI l _) <- getInput
  let offset = srcLocCol (psRealLoc l) - len
  ctx <- getContext
  case ctx of
      Layout prev_off _ : _ | prev_off >= offset -> do
        pushLexState layout_left
        return (L span tok)
      _ -> do
        setContext (Layout offset gen_semic : ctx)
        return (L span tok)

do_layout_left :: Action
do_layout_left span _buf _len _buf2 = do
  _ <- popLexState
  pushLexState bol
  return (L span ITclayout)

-- -----------------------------------------------------------------------------
-- Strings & Chars

lex_string_tok :: Action
lex_string_tok span buf _len _buf2 = do
  lexed <- lex_string
  (AI end bufEnd) <- getInput
  let tok = ITstring (SourceText src) (mkFastString lexed)
      src = lexemeToFastString buf (cur bufEnd - cur buf)
  return $ L (mkPsSpan (psSpanStart span) end) tok

lex_string :: P String
lex_string = do
  start <- getInput
  lex_string_helper "" start

lex_string_helper :: String -> AlexInput -> P String
lex_string_helper s start = do
  i <- getInput
  case alexGetChar' i of
    Nothing -> lit_error i
    Just ('"', i) -> do
      setInput i
      return (reverse s)
    Just ('\\', i)
        | Just ('&', i) <- next -> do
                setInput i
                lex_string_helper s start
        | Just (c, i) <- next, c <= '\x7f' && is_space c -> do
                setInput i
                lex_stringgap s start
        where next = alexGetChar' i
    Just (c, i1) -> do
        case c of
          '\\' -> do
            setInput i1
            c' <- lex_escape
            lex_string_helper (c':s) start
          c | isAny c -> do
            setInput i1
            lex_string_helper (c:s) start
          _ | any isDoubleSmartQuote s -> do
            setInput start
            advance_to_smart_quote_character
            i2@(AI loc _) <- getInput
            case alexGetChar' i2 of
              Just (c, _) -> do
                add_nonfatal_smart_quote_error c loc
                lit_error i
              Nothing -> lit_error i
          _ -> lit_error i

lex_stringgap :: String -> AlexInput -> P String
lex_stringgap s start = do
  i <- getInput
  c <- getCharOrFail i
  case c of
    '\\' -> lex_string_helper s start
    c | c <= '\x7f' && is_space c -> lex_stringgap s start
    _ -> lit_error i

lex_char_tok :: Action
lex_char_tok span buf _len _buf2 = do
  i1 <- getInput
  let loc = psSpanStart span
  case alexGetChar' i1 of
    Nothing -> lit_error i1
    Just ('\\', i2@(AI end2 _)) -> do
      setInput i2
      lit_ch <- lex_escape
      i3 <- getInput
      mc <- getCharOrFail i3
      if mc == '\''
        then finish_char_tok buf loc lit_ch
        else if isSingleSmartQuote mc
               then add_smart_quote_error mc end2
               else lit_error i3
    Just (c, i2@(AI end2 _))
            | not (isAny c) -> lit_error i1
            | otherwise -> case alexGetChar' i2 of
                Just ('\'', i3) -> do
                  setInput i3
                  finish_char_tok buf loc c
                Just (c, _) | isSingleSmartQuote c -> add_smart_quote_error c end2
                _ -> lit_error i1 -- potentially should be lit_error i2

finish_char_tok :: StringBuffer -> PsLoc -> Char -> P (PsLocated Token)
finish_char_tok buf loc ch = do
  AI end bufEnd <- getInput
  let src = lexemeToFastString buf (cur bufEnd - cur buf)
  return (L (mkPsSpan loc end) (ITchar (SourceText src) ch))

isAny :: Char -> Bool
isAny c | c > '\x7f' = isPrint c
        | otherwise  = is_any c

lex_escape :: P Char
lex_escape = do
  i0@(AI loc _) <- getInput
  c <- getCharOrFail i0
  case c of
    'a' -> return '\a'
    'b' -> return '\b'
    'f' -> return '\f'
    'n' -> return '\n'
    'r' -> return '\r'
    't' -> return '\t'
    'v' -> return '\v'
    '\\'-> return '\\'
    '"' -> return '\"'
    '\''-> return '\''
    smart_double_quote | isDoubleSmartQuote smart_double_quote ->
      add_smart_quote_error smart_double_quote loc
    smart_single_quote | isSingleSmartQuote smart_single_quote ->
      add_smart_quote_error smart_single_quote loc
    '^'   -> do i1 <- getInput
                c <- getCharOrFail i1
                if c >= '@' && c <= '_'
                    then return (chr (ord c - ord '@'))
                    else lit_error i1
    'x'   -> readNum is_hexdigit 16 hexDigit
    'o'   -> readNum is_octdigit  8 octDecDigit
    x | is_decdigit x -> readNum2 is_decdigit 10 octDecDigit (octDecDigit x)
    c1 ->  do
      i <- getInput
      case alexGetChar' i of
        Nothing -> lit_error i0
        Just (c2,i2) ->
          case alexGetChar' i2 of
            Nothing -> do lit_error i0
            Just (c3,i3) ->
              let str = [c1,c2,c3] in
              case [ (c,rest) | (p,c) <- silly_escape_chars,
                                Just rest <- [stripPrefix p str] ] of
                     (escape_char,[]):_ -> do
                       setInput i3
                       return escape_char
                     (escape_char,_:_):_ -> do
                       setInput i2
                       return escape_char
                     [] -> lit_error i0

readNum :: (Char -> Bool) -> Int -> (Char -> Int) -> P Char
readNum is_digit base conv = do
  i <- getInput
  c <- getCharOrFail i
  if is_digit c
    then readNum2 is_digit base conv (conv c)
    else lit_error i

readNum2 :: (Char -> Bool) -> Int -> (Char -> Int) -> Int -> P Char
readNum2 is_digit base conv i = do
  input <- getInput
  read i input
  where read i input = do
          case alexGetChar' input of
            Just (c, input') | is_digit c -> do
              let i' = i*base + conv c
              if i' > 0x10ffff
                then setInput input >> lexError LexNumEscapeRange
                else read i' input'
            _ -> do
              setInput input
              return (chr i)

silly_escape_chars :: [(String, Char)]
silly_escape_chars = [
        ("NUL", '\NUL'),
        ("SOH", '\SOH'),
        ("STX", '\STX'),
        ("ETX", '\ETX'),
        ("EOT", '\EOT'),
        ("ENQ", '\ENQ'),
        ("ACK", '\ACK'),
        ("BEL", '\BEL'),
        ("BS", '\BS'),
        ("HT", '\HT'),
        ("LF", '\LF'),
        ("VT", '\VT'),
        ("FF", '\FF'),
        ("CR", '\CR'),
        ("SO", '\SO'),
        ("SI", '\SI'),
        ("DLE", '\DLE'),
        ("DC1", '\DC1'),
        ("DC2", '\DC2'),
        ("DC3", '\DC3'),
        ("DC4", '\DC4'),
        ("NAK", '\NAK'),
        ("SYN", '\SYN'),
        ("ETB", '\ETB'),
        ("CAN", '\CAN'),
        ("EM", '\EM'),
        ("SUB", '\SUB'),
        ("ESC", '\ESC'),
        ("FS", '\FS'),
        ("GS", '\GS'),
        ("RS", '\RS'),
        ("US", '\US'),
        ("SP", '\SP'),
        ("DEL", '\DEL')
        ]

lit_error :: AlexInput -> P a
lit_error i = do
  setInput i
  lexError LexStringCharLit

getCharOrFail :: AlexInput -> P Char
getCharOrFail i = case alexGetChar' i of
  Nothing -> lexError LexStringCharLitEOF
  Just (c, i) -> do setInput i; return c

-- -----------------------------------------------------------------------------
-- Unicode Smart Quote detection

isDoubleSmartQuote :: Char -> Bool
isDoubleSmartQuote '“' = True
isDoubleSmartQuote '”' = True
isDoubleSmartQuote _ = False

isSingleSmartQuote :: Char -> Bool
isSingleSmartQuote '‘' = True
isSingleSmartQuote '’' = True
isSingleSmartQuote _ = False

isSmartQuote :: AlexAccPred ExtsBitmap
isSmartQuote _ _ _ (AI _ buf) =
  let c = prevChar buf ' '
  in isSingleSmartQuote c || isDoubleSmartQuote c

smart_quote_error_message :: Char -> PsLoc -> MsgEnvelope PsMessage
smart_quote_error_message c loc =
  let (correct_char, correct_char_name) =
         if isSingleSmartQuote c
           then ('\'', "Single Quote")
           else ('"', "Quotation Mark")
      err = mkPlainErrorMsgEnvelope (mkSrcSpanPs (mkPsSpan loc loc)) $
              PsErrUnicodeCharLooksLike c correct_char correct_char_name
  in err

smart_quote_error :: Action
smart_quote_error span buf _len _buf2 = do
  let c = currentChar buf
  addFatalError (smart_quote_error_message c (psSpanStart span))

add_smart_quote_error :: Char -> PsLoc -> P a
add_smart_quote_error c loc = addFatalError (smart_quote_error_message c loc)

add_nonfatal_smart_quote_error :: Char -> PsLoc -> P ()
add_nonfatal_smart_quote_error c loc = addError (smart_quote_error_message c loc)

advance_to_smart_quote_character :: P ()
advance_to_smart_quote_character  = do
  i <- getInput
  case alexGetChar' i of
    Just (c, _) | isDoubleSmartQuote c -> return ()
    Just (_, i2) -> do setInput i2; advance_to_smart_quote_character
    Nothing -> return () -- should never get here

-- -----------------------------------------------------------------------------
-- Warnings

warnTab :: Action
warnTab srcspan _buf _len _buf2 = do
  addTabWarning (psRealSpan srcspan)
  lexToken

-- -----------------------------------------------------------------------------
-- The Parse Monad

type GenSemic = Bool

generateSemic :: GenSemic
generateSemic = True

dontGenerateSemic :: GenSemic
dontGenerateSemic = False

data LayoutContext
  = NoLayout
  | Layout !Int !GenSemic

newtype ParseResult a = PR (# (# PState, a #) | PState #)

pattern POk :: PState -> a -> ParseResult a
pattern POk s a = PR (# (# s , a #) | #)

pattern PFailed :: PState -> ParseResult a
pattern PFailed s = PR (# | s #)

{-# COMPLETE POk, PFailed #-}

warnopt :: WarningFlag -> ParserOpts -> Bool
warnopt f options = f `EnumSet.member` pWarningFlags options

data ParserOpts = ParserOpts
  { pDiagOpts :: !DiagOpts
  , pRawTokStream :: !Bool
  }

pWarningFlags :: ParserOpts -> EnumSet WarningFlag
pWarningFlags opts = diag_warning_flags (pDiagOpts opts)

data PState = PState
  { buffer :: StringBuffer
  , options :: ParserOpts
  , errors :: Messages PsMessage
  , warnings :: Messages PsMessage
  , tab_first :: Strict.Maybe RealSrcSpan
  , tab_count :: !Word
  , last_tk :: Strict.Maybe (PsLocated Token)
  , prev_loc :: PsSpan
  , last_loc :: PsSpan
  , last_len :: !Int
  , loc :: PsLoc
  , context :: [LayoutContext]
  , lex_state :: [Int]
  , srcfiles :: [FastString]

  , eof_pos :: Strict.Maybe (Strict.Pair RealSrcSpan RealSrcSpan)
  , header_comments :: Strict.Maybe [LEpaComment]
  , comment_q :: [LEpaComment]
  }

newtype P a = P { unP :: PState -> ParseResult a }

instance Functor P where
  fmap = liftM

instance Applicative P where
  pure = returnP
  (<*>) = ap

instance Monad P where
  (>>=) = thenP

returnP :: a -> P a
returnP a = a `seq` (P $ \s -> POk s a)

thenP :: P a -> (a -> P b) -> P b
(P m) `thenP` k = P $ \ s ->
  case m s of
    POk s1 a -> (unP (k a)) s1
    PFailed s1 -> PFailed s1

failMsgP :: (SrcSpan -> MsgEnvelope PsMessage) -> P a
failMsgP f = do
  pState <- getPState
  addFatalError (f (mkSrcSpanPs (last_loc pState)))

failLocMsgP :: RealSrcLoc -> RealSrcLoc -> (SrcSpan -> MsgEnvelope PsMessage) -> P a
failLocMsgP loc1 loc2 f =
  addFatalError (f (RealSrcSpan (mkRealSrcSpan loc1 loc2) Strict.Nothing))

getPState :: P PState
getPState = P $ \ s -> POk s s

getRealSrcLoc :: P RealSrcLoc
getRealSrcLoc = P $ \ s@PState{loc=loc} -> POk s (psRealLoc loc)

setEofPos :: RealSrcSpan -> RealSrcSpan -> P ()
setEofPos span gap = P $ \ s ->
  POk s{ eof_pos = Strict.Just (span `Strict.And` gap) } ()

setLastToken :: PsSpan -> Int -> P ()
setLastToken loc len = P $ \ s ->
  POk s
  { last_loc = loc
  , last_len = len
  } ()

setLastTk :: PsLocated Token -> P ()
setLastTk tk@(L l _) = P $ \ s ->
  if isPointRealSpan (psRealSpan l)
    then POk s{ last_tk = Strict.Just tk } ()
    else POk s{ last_tk = Strict.Just tk
              , prev_loc = l } ()

setLastComment :: PsLocated Token -> P ()
setLastComment (L l _) = P $ \ s -> POk s{ prev_loc = l } ()

getLastLocIncludingComments :: P PsSpan
getLastLocIncludingComments = P $ \ s@(PState { prev_loc = prev_loc }) ->
  POk s prev_loc

data AlexInput = AI !PsLoc !StringBuffer

{-# INLINE adjustChar #-}
adjustChar :: Char -> Word8
adjustChar c = adj_c
  where non_graphic     = 0x00
        upper           = 0x01
        lower           = 0x02
        digit           = 0x03
        symbol          = 0x04
        space           = 0x05
        other_graphic   = 0x06
        uniidchar       = 0x07

        adj_c
          | c <= '\x07' = non_graphic
          | c <= '\x7f' = fromIntegral (ord c)
          -- Alex doesn't handle Unicode, so when Unicode
          -- character is encountered we output these values
          -- with the actual character value hidden in the state.
          | otherwise =
                case generalCategory c of
                  UppercaseLetter       -> upper
                  LowercaseLetter       -> lower
                  TitlecaseLetter       -> upper
                  ModifierLetter        -> uniidchar
                  OtherLetter           -> lower
                  NonSpacingMark        -> uniidchar
                  SpacingCombiningMark  -> other_graphic
                  EnclosingMark         -> other_graphic
                  DecimalNumber         -> digit
                  LetterNumber          -> digit
                  OtherNumber           -> digit
                  ConnectorPunctuation  -> symbol
                  DashPunctuation       -> symbol
                  OpenPunctuation       -> other_graphic
                  ClosePunctuation      -> other_graphic
                  InitialQuote          -> other_graphic
                  FinalQuote            -> other_graphic
                  OtherPunctuation      -> symbol
                  MathSymbol            -> symbol
                  CurrencySymbol        -> symbol
                  ModifierSymbol        -> symbol
                  OtherSymbol           -> symbol
                  Space                 -> space
                  _other                -> non_graphic

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar (AI _ buf) = unsafeChr (fromIntegral (adjustChar pc))
  where pc = prevChar buf '\n'

unsafeChr :: Int -> Char
unsafeChr (I# c) = GHC.Exts.C# (GHC.Exts.chr# c)

alexGetChar :: AlexInput -> Maybe (Char, AlexInput)
alexGetChar inp = case alexGetByte inp of
                    Nothing -> Nothing
                    Just (b, i) -> c `seq` Just (c, i)
                      where c = unsafeChr $ fromIntegral b

alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte (AI loc s)
  | atEnd s = Nothing
  | otherwise = byte `seq` loc' `seq` s' `seq`
                Just (byte, (AI loc' s'))
  where (c, s') = nextChar s
        loc' = advancePsLoc loc c
        byte = adjustChar c

{-# INLINE alexGetChar' #-}
alexGetChar' :: AlexInput -> Maybe (Char, AlexInput)
alexGetChar' (AI loc s)
  | atEnd s = Nothing
  | otherwise = c `seq` loc' `seq` s' `seq`
                Just (c, (AI loc' s'))
  where (c, s') = nextChar s
        loc' = advancePsLoc loc c

getInput :: P AlexInput
getInput = P $ \ s@PState { loc = l, buffer = b } -> POk s (AI l b)

setInput :: AlexInput -> P ()
setInput (AI l b) = P $ \ s -> POk s { loc = l, buffer = b} ()

nextIsEOF :: P Bool
nextIsEOF = do
  AI _ s <- getInput
  return $ atEnd s

pushLexState :: Int -> P ()
pushLexState ls = P $ \ s@PState{ lex_state = l } -> POk s{ lex_state = ls : l } ()

popLexState :: P Int
popLexState = P $ \ s@PState { lex_state = ls : l } -> POk s { lex_state = l } ls

getLexState :: P Int
getLexState = P $ \ s@PState { lex_state = ls : _ } -> POk s ls

type ExtsBitmap = Word64

{-# INLINE mkParserOpts #-}
mkParserOpts
  :: DiagOpts
  -> Bool      -- keep regular comment tokens
  -> ParserOpts
mkParserOpts diag_opts !rawTokStream =
  ParserOpts
  { pDiagOpts = diag_opts
  , pRawTokStream = rawTokStream
  }

initPragState :: ParserOpts -> StringBuffer -> RealSrcLoc -> PState
initPragState options buf loc = (initParserState options buf loc)
  --{ lex_state = [bol, option_prags, 0] }

initParserState :: ParserOpts -> StringBuffer -> RealSrcLoc -> PState
initParserState options buf loc = 
  PState
  { buffer = buf
  , options = options
  , errors = emptyMessages
  , warnings = emptyMessages
  , tab_first = Strict.Nothing
  , tab_count = 0
  , last_tk = Strict.Nothing
  , prev_loc = mkPsSpan init_loc init_loc
  , last_loc = mkPsSpan init_loc init_loc
  , last_len = 0
  , loc = init_loc
  , context = []
  , lex_state = [bol, 0]
  , srcfiles = []
  , eof_pos = Strict.Nothing
  , header_comments = Strict.Nothing
  , comment_q = []
  }
  where init_loc = PsLoc loc (BufPos 0)

class Monad m => MonadP m where
  addError :: MsgEnvelope PsMessage -> m ()
  addWarning :: MsgEnvelope PsMessage -> m ()
  addFatalError :: MsgEnvelope PsMessage -> m a
  isRawTokenStream :: m Bool
  allocateCommentsP :: RealSrcSpan -> m EpAnnComments
  allocatePriorCommentsP :: RealSrcSpan -> m EpAnnComments
  allocateFinalCommentsP :: RealSrcSpan -> m EpAnnComments

instance MonadP P where
  addError err
    = P $ \ s -> POk s { errors = err `addMessage` errors s } ()
  addWarning w
    = P $ \ s -> POk s { warnings = w `addMessage` warnings s } ()
  addFatalError err
    = addError err >> P PFailed
  isRawTokenStream
    = P $ \ s -> let b = pRawTokStream $ options s
                 in b `seq` POk s b
  allocateCommentsP ss = P $ \s ->
    if null (comment_q s) then POk s emptyComments else  -- fast path
    let (comment_q', newAnns) = allocateComments ss (comment_q s) in
      POk s {
         comment_q = comment_q'
       } (EpaComments newAnns)
  allocatePriorCommentsP ss = P $ \s ->
    let (header_comments', comment_q', newAnns)
             = allocatePriorComments ss (comment_q s) (header_comments s) in
      POk s {
         header_comments = header_comments',
         comment_q = comment_q'
       } (EpaComments newAnns)
  allocateFinalCommentsP ss = P $ \s ->
    let (header_comments', comment_q', newAnns)
             = allocateFinalComments ss (comment_q s) (header_comments s) in
      POk s {
         header_comments = header_comments',
         comment_q = comment_q'
       } (EpaCommentsBalanced (Strict.fromMaybe [] header_comments') newAnns)

getCommentsFor :: (MonadP m) => SrcSpan -> m EpAnnComments
getCommentsFor (RealSrcSpan l _) = allocateCommentsP l
getCommentsFor _ = return emptyComments

getPriorCommentsFor :: (MonadP m) => SrcSpan -> m EpAnnComments
getPriorCommentsFor (RealSrcSpan l _) = allocatePriorCommentsP l
getPriorCOmmentsFor _ = return emptyComments

getFinalCommentsFor :: (MonadP m) => SrcSpan -> m EpAnnComments
getFinalCommentsFor (RealSrcSpan l _) = allocateFinalCommentsP l
getFinalCommentsFor _ = return emptyComments

getEofPos :: P (Strict.Maybe (Strict.Pair RealSrcSpan RealSrcSpan))
getEofPos = P $ \s@(PState { eof_pos = pos }) -> POk s pos

addPsMessage :: SrcSpan -> PsMessage -> P ()
addPsMessage srcspan msg = do
  diag_opts <- (pDiagOpts . options) <$> getPState
  addWarning (mkPlainMsgEnvelope diag_opts srcspan msg)

addTabWarning :: RealSrcSpan -> P ()
addTabWarning srcspan
 = P $ \s@PState{tab_first=tf, tab_count=tc, options=o} ->
       let tf' = tf <|> Strict.Just srcspan
           tc' = tc + 1
           s' = if warnopt Opt_WarnTabs o
                then s{tab_first = tf', tab_count = tc'}
                else s
       in POk s' ()

getPsErrorMessages :: PState -> Messages PsMessage
getPsErrorMessages p = errors p

getPsMessages :: PState -> (Messages PsMessage, Messages PsMessage)
getPsMessages p =
  let ws = warnings p
      diag_opts = pDiagOpts (options p)
      -- we add the tabulation warning on the fly because
      -- we count the number of occurrences of tab characters
      ws' = case tab_first p of
        Strict.Nothing -> ws
        Strict.Just tf ->
          let msg = mkPlainMsgEnvelope diag_opts
                          (RealSrcSpan tf Strict.Nothing)
                          (PsWarnTab (tab_count p))
          in msg `addMessage` ws
  in (ws', errors p)

getContext :: P [LayoutContext]
getContext = P $ \ s@PState{ context = ctx } -> POk s ctx

setContext :: [LayoutContext] -> P ()
setContext ctx = P $ \s -> POk s{context=ctx} ()

popContext :: P ()
popContext = P $ \ s@(PState{ buffer = buf, options = o, context = ctx,
                              last_len = len, last_loc = last_loc }) ->
  case ctx of
        (_:tl) ->
          POk s{ context = tl } ()
        []     ->
          unP (addFatalError $ srcParseErr o buf len (mkSrcSpanPs last_loc)) s

pushCurrentContext :: GenSemic -> P ()
pushCurrentContext gen_semic = P $ \ s@PState{ last_loc=loc, context=ctx } ->
    POk s{context = Layout (srcSpanStartCol (psRealSpan loc)) gen_semic : ctx} ()

pushModuleContext :: P ()
pushModuleContext = pushCurrentContext generateSemic

getOffside :: P (Ordering, Bool)
getOffside = P $ \s@PState{last_loc=loc, context=stk} ->
                let offs = srcSpanStartCol (psRealSpan loc) in
                let ord = case stk of
                            Layout n gen_semic : _ ->
                              (compare offs n, gen_semic)
                            _ ->
                              (GT, dontGenerateSemic)
                in POk s ord

-- ---------------------------------------------------------------------------
-- Construct a parse error

srcParseErr
  :: ParserOpts
  -> StringBuffer
  -> Int
  -> SrcSpan
  -> MsgEnvelope PsMessage
srcParseErr options buf len loc =
    mkPlainErrorMsgEnvelope loc (PsErrParse token details)
  where
    token = lexemeToString (offsetBytes (-len) buf) len
    details = PsErrParseDetails
 
srcParseFail :: P a
srcParseFail = P $ \ s@PState { buffer = buf, options = o, last_len = len,
                                last_loc = last_loc } ->
  unP (addFatalError $ srcParseErr o buf len (mkSrcSpanPs last_loc)) s

lexError :: LexErr -> P a
lexError e = do
  loc <- getRealSrcLoc
  (AI end buf) <- getInput
  reportLexError loc (psRealLoc end) buf
    (\ k srcLoc -> mkPlainErrorMsgEnvelope srcLoc $ PsErrLexer e k)

lexer :: Bool -> (Located Token -> P a) -> P a
lexer queueComments cont = do
  (L span tok) <- lexToken
  if (queueComments && isComment tok)
    then queueComment (L (psRealSpan span) tok) >> lexer queueComments cont
    else cont (L (mkSrcSpanPs span) tok)

lexerDbg :: Bool -> (Located Token -> P a) -> P a
lexerDbg queueComments cont = lexer queueComments contDbg
  where
    contDbg tok = trace ("token: " ++ show (unLoc tok)) (cont tok)

lexToken :: P (PsLocated Token)
lexToken = do
  inp@(AI loc1 buf) <- getInput
  sc <- getLexState
  case alexScan inp sc of
    AlexEOF -> do
      let span = mkPsSpan loc1 loc1
      lc <- getLastLocIncludingComments
      setEofPos (psRealSpan span) (psRealSpan lc)
      setLastToken span 0
      return (L span ITeof)
    AlexError (AI loc2 buf) ->
      reportLexError (psRealLoc loc1) (psRealLoc loc2) buf
        (\ k srcLoc -> mkPlainErrorMsgEnvelope srcLoc $ PsErrLexer LexError k)
    AlexSkip inp2 _ -> do
      setInput inp2
      lexToken
    AlexToken inp2@(AI end buf2) _ t -> do
      setInput inp2
      let span = mkPsSpan loc1 end
          bytes = byteDiff buf buf2
      span `seq` setLastToken span bytes
      lt <- t span buf bytes buf2
      let lt' = unLoc lt
      if (isComment lt') then setLastComment lt else setLastTk lt
      return lt

reportLexError
  :: RealSrcLoc
  -> RealSrcLoc
  -> StringBuffer
  -> (LexErrKind -> SrcSpan -> MsgEnvelope PsMessage)
  -> P a
reportLexError loc1 loc2 buf f
  | atEnd buf = failLocMsgP loc1 loc2 (f LexErrKind_EOF)
  | otherwise =
  let c = fst (nextChar buf)
  in if c == '\0'
     then failLocMsgP loc2 loc2 (f LexErrKind_UTF8)
     else failLocMsgP loc1 loc2 (f (LexErrKind_Char c))

lexTokenStream
  :: ParserOpts
  -> StringBuffer
  -> RealSrcLoc
  -> ParseResult [Located Token]
lexTokenStream opts buf loc = unP go initState { options = opts' }
  where
    opts' = opts { pRawTokStream = True }
    initState = initParserState opts' buf loc
    go = do
      ltok <- lexer False return
      case ltok of
        L _ ITeof -> return []
        _ -> liftM (ltok:) go

-- -----------------------------------------------------------------------------
-- Helper functions for generating annotations in the parser

mkParensEpAnn :: RealSrcSpan -> (AddEpAnn, AddEpAnn)
mkParensEpAnn span = (AddEpAnn AnnOpenP (EpaSpan (RealSrcSpan lo Strict.Nothing)),
                      AddEpAnn AnnCloseP (EpaSpan (RealSrcSpan lc Strict.Nothing)))
  where
    f = srcSpanFile span
    sl = srcSpanStartLine span
    sc = srcSpanStartCol span
    el = srcSpanEndLine span
    ec = srcSpanEndCol span
    lo = mkRealSrcSpan (realSrcSpanStart span) (mkRealSrcLoc f sl (sc+1))
    lc = mkRealSrcSpan (mkRealSrcLoc f el (ec - 1)) (realSrcSpanEnd span)

queueComment :: RealLocated Token -> P ()
queueComment c = P $ \ s -> POk s {
    comment_q = commentToAnnotation c : comment_q s
  } ()

allocateComments
  :: RealSrcSpan
  -> [LEpaComment]
  -> ([LEpaComment], [LEpaComment])
allocateComments span comment_q =
  let (before, rest) = break (\ (L l _) -> isRealSubspanOf (anchor l) span) comment_q
      (middle, after) = break (\ (L l _) -> not (isRealSubspanOf (anchor l) span)) rest
      comment_q' = before ++ after
      newAnns = middle
  in (comment_q', reverse newAnns)

splitPriorComments
  :: RealSrcSpan
  -> [LEpaComment]
  -> ([LEpaComment], [LEpaComment])
splitPriorComments span prior_comments =
  let cmp :: RealSrcSpan -> LEpaComment -> Bool
      cmp later (L l c)
        = srcSpanStartLine later - srcSpanEndLine (anchor l) == 1
          && srcSpanEndLine (ac_prior_tok c) /= srcSpanStartLine (anchor l)
      go :: [LEpaComment] -> RealSrcSpan -> [LEpaComment]
         -> ([LEpaComment], [LEpaComment])
      go decl_comments _ [] = ([], decl_comments)
      go decl_comments r (c@(L l _):cs) = if cmp r c
        then go (c:decl_comments) (anchor l) cs
        else (reverse (c:cs), decl_comments)
  in go [] span prior_comments

allocatePriorComments
  :: RealSrcSpan
  -> [LEpaComment]
  -> Strict.Maybe [LEpaComment]
  -> (Strict.Maybe [LEpaComment], [LEpaComment], [LEpaComment])
allocatePriorComments span comment_q mheader_comments =
  let cmp (L l _) = anchor l <= span
      (newAnns, after) = partition cmp comment_q
      comment_q' = after
      (prior_comments, decl_comments) = splitPriorComments span newAnns
  in case mheader_comments of
       Strict.Nothing -> (Strict.Just prior_comments, comment_q', decl_comments)
       Strict.Just _ -> (mheader_comments, comment_q', reverse newAnns)

allocateFinalComments
  :: RealSrcSpan
  -> [LEpaComment]
  -> Strict.Maybe [LEpaComment]
  -> (Strict.Maybe [LEpaComment], [LEpaComment], [LEpaComment])
allocateFinalComments _ss comment_q mheader_comments =
  case mheader_comments of
    Strict.Nothing -> (Strict.Just (reverse comment_q), [], [])
    Strict.Just _ -> (mheader_comments, [], reverse comment_q)

commentToAnnotation :: RealLocated Token -> LEpaComment
commentToAnnotation (L l (ITlineComment s ll))  = mkLEpaComment l ll (EpaLineComment s)
commentToAnnotation (L l (ITblockComment s ll)) = mkLEpaComment l ll (EpaBlockComment s)
commentToAnnotation _                           = panic "commentToAnnotation"

mkLEpaComment :: RealSrcSpan -> PsSpan -> EpaCommentTok -> LEpaComment
mkLEpaComment l ll tok = L (realSpanAsAnchor l) (EpaComment tok (psRealSpan ll))

isComment :: Token -> Bool
isComment (ITlineComment _ _) = True
isComment (ITblockComment _ _) = True
isComment _ = False

}
