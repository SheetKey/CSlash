{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}

module CSlash.Types.Error
   ( Messages
   , mkMessages
   , getMessages
   , emptyMessages
   , isEmptyMessages
   , singleMessage
   , addMessage
   , unionMessages
   , unionManyMessages
   , filterMessages
   , MsgEnvelope (..)

   , MessageClass (..)
   , Severity (..)
   , Diagnostic (..)
   , UnknownDiagnostic (..)
   , mkSimpleUnknownDiagnostic
   , mkUnknownDiagnostic
   , embedUnknownDiagnostic
   , DiagnosticMessage (..)
   , DiagnosticReason (WarningWithFlag, ..)
   , ResolvedDiagnosticReason(..)
   , DiagnosticHint (..)
   , mkPlainDiagnostic
   , mkPlainError
   , mkDecoratedDiagnostic
   , mkDecoratedError

   , pprDiagnostic

   , HasDefaultDiagnosticOpts(..)
   , defaultDiagnosticOpts
   , NoDiagnosticOpts(..)

   , CSlashHint (..)
   , AvailableBindings(..)
   , noHints

   , SDoc
   , DecoratedSDoc (unDecorated)
   , mkDecorated, mkSimpleDecorated
   , unionDecoratedSDoc
   , mapDecoratedSDoc

   , pprMessageBag
   , mkLocMessage
   , mkLocMessageWarningGroups
   , getCaretDiagnostic
   , isIntrinsicErrorMessage
   , isExtrinsicErrorMessage
   , isWarningMessage
   , getErrorMessages
   , getWarningMessages
   , partitionMessages
   , errorsFound
   , errorsOrFatalWarningsFound

   , DiagnosticCode(..)
   )
where

import Prelude hiding ((<>))

import CSlash.Driver.Flags

import CSlash.Data.Bag
import GHC.IO (catchException)
import CSlash.Utils.Outputable as Outputable
import qualified CSlash.Utils.Ppr.Color as Col
import CSlash.Types.SrcLoc as SrcLoc
import CSlash.Types.Hint
import CSlash.Data.FastString (unpackFS)
import CSlash.Data.StringBuffer (atLine, hGetStringBuffer, len, lexemeToString)
import CSlash.Utils.Panic
import CSlash.Unit.Module.Warnings (WarningCategory)
import Data.Bifunctor
import Data.Foldable    ( fold, toList )
import Data.List.NonEmpty ( NonEmpty (..) )
import qualified Data.List.NonEmpty as NE
import Data.List ( intercalate )
import Data.Typeable ( Typeable )
import Numeric.Natural ( Natural )
import Text.Printf ( printf )
import CSlash.Version (cProjectVersion)
import CSlash.Types.Hint.Ppr () -- Outputtable instance

newtype Messages e = Messages { getMessages :: Bag (MsgEnvelope e) }
  deriving newtype (Semigroup, Monoid)
  deriving stock (Functor, Foldable, Traversable)

emptyMessages :: Messages e
emptyMessages = Messages emptyBag

mkMessages :: Bag (MsgEnvelope e) -> Messages e
mkMessages = Messages . filterBag interesting
  where
    interesting :: MsgEnvelope e -> Bool
    interesting = (/=) SevIgnore . errMsgSeverity

isEmptyMessages :: Messages e -> Bool
isEmptyMessages (Messages msgs) = isEmptyBag msgs

singleMessage :: MsgEnvelope e -> Messages e
singleMessage e = addMessage e emptyMessages

instance Diagnostic e => Outputable (Messages e) where
  ppr msgs = braces (vcat (map ppr_one (bagToList (getMessages msgs))))
     where
       ppr_one :: MsgEnvelope e -> SDoc
       ppr_one envelope =
        vcat [ text "Resolved:" <+> ppr (errMsgReason envelope),
               pprDiagnostic (errMsgDiagnostic envelope)
             ]

addMessage :: MsgEnvelope e -> Messages e -> Messages e
addMessage x (Messages xs)
  | SevIgnore <- errMsgSeverity x = Messages xs
  | otherwise                     = Messages (x `consBag` xs)

unionMessages :: Messages e -> Messages e -> Messages e
unionMessages (Messages msgs1) (Messages msgs2) =
  Messages (msgs1 `unionBags` msgs2)

unionManyMessages :: Foldable f => f (Messages e) -> Messages e
unionManyMessages = fold

filterMessages :: (MsgEnvelope e -> Bool) -> Messages e -> Messages e
filterMessages f (Messages msgs) =
  Messages (filterBag f msgs)

newtype DecoratedSDoc = Decorated { unDecorated :: [SDoc] }

mkDecorated :: [SDoc] -> DecoratedSDoc
mkDecorated = Decorated

mkSimpleDecorated :: SDoc -> DecoratedSDoc
mkSimpleDecorated doc = Decorated [doc]

unionDecoratedSDoc :: DecoratedSDoc -> DecoratedSDoc -> DecoratedSDoc
unionDecoratedSDoc (Decorated s1) (Decorated s2) =
  Decorated (s1 `mappend` s2)

mapDecoratedSDoc :: (SDoc -> SDoc) -> DecoratedSDoc -> DecoratedSDoc
mapDecoratedSDoc f (Decorated s1) =
  Decorated (map f s1)

class HasDefaultDiagnosticOpts opts where
  defaultOpts :: opts

defaultDiagnosticOpts :: forall opts . HasDefaultDiagnosticOpts (DiagnosticOpts opts) => DiagnosticOpts opts
defaultDiagnosticOpts = defaultOpts @(DiagnosticOpts opts)

class (HasDefaultDiagnosticOpts (DiagnosticOpts a)) => Diagnostic a where
  type DiagnosticOpts a
  diagnosticMessage :: DiagnosticOpts a -> a -> DecoratedSDoc
  diagnosticReason  :: a -> DiagnosticReason
  diagnosticHints   :: a -> [CSlashHint]
  diagnosticCode    :: a -> Maybe DiagnosticCode

data UnknownDiagnostic opts where
  UnknownDiagnostic :: (Diagnostic a, Typeable a)
                    => (opts -> DiagnosticOpts a) 
                    -> a
                    -> UnknownDiagnostic opts
instance HasDefaultDiagnosticOpts opts => Diagnostic (UnknownDiagnostic opts) where
  type DiagnosticOpts (UnknownDiagnostic opts) = opts
  diagnosticMessage opts (UnknownDiagnostic f diag) = diagnosticMessage (f opts) diag
  diagnosticReason    (UnknownDiagnostic _ diag) = diagnosticReason  diag
  diagnosticHints     (UnknownDiagnostic _ diag) = diagnosticHints   diag
  diagnosticCode      (UnknownDiagnostic _ diag) = diagnosticCode    diag

data NoDiagnosticOpts = NoDiagnosticOpts
instance HasDefaultDiagnosticOpts NoDiagnosticOpts where
  defaultOpts = NoDiagnosticOpts

mkSimpleUnknownDiagnostic :: (Diagnostic a, Typeable a, DiagnosticOpts a ~ NoDiagnosticOpts) => a -> UnknownDiagnostic b
mkSimpleUnknownDiagnostic = UnknownDiagnostic (const NoDiagnosticOpts)

mkUnknownDiagnostic :: (Typeable a, Diagnostic a) => a -> UnknownDiagnostic (DiagnosticOpts a)
mkUnknownDiagnostic = UnknownDiagnostic id

embedUnknownDiagnostic :: (Diagnostic a, Typeable a) => (opts -> DiagnosticOpts a) -> a -> UnknownDiagnostic opts
embedUnknownDiagnostic = UnknownDiagnostic

--------------------------------------------------------------------------------

pprDiagnostic :: forall e . Diagnostic e => e -> SDoc
pprDiagnostic e = vcat [ ppr (diagnosticReason e)
                       , nest 2 (vcat (unDecorated (diagnosticMessage opts e))) ]
  where opts = defaultDiagnosticOpts @e

data DiagnosticHint = DiagnosticHint !SDoc

instance Outputable DiagnosticHint where
  ppr (DiagnosticHint msg) = msg

data DiagnosticMessage = DiagnosticMessage
  { diagMessage :: !DecoratedSDoc
  , diagReason  :: !DiagnosticReason
  , diagHints   :: [CSlashHint]
  }

instance Diagnostic DiagnosticMessage where
  type DiagnosticOpts DiagnosticMessage = NoDiagnosticOpts
  diagnosticMessage _ = diagMessage
  diagnosticReason  = diagReason
  diagnosticHints   = diagHints
  diagnosticCode _  = Nothing

noHints :: [CSlashHint]
noHints = mempty

mkPlainDiagnostic :: DiagnosticReason -> [CSlashHint] -> SDoc -> DiagnosticMessage
mkPlainDiagnostic rea hints doc = DiagnosticMessage (mkSimpleDecorated doc) rea hints

mkPlainError :: [CSlashHint] -> SDoc -> DiagnosticMessage
mkPlainError hints doc = DiagnosticMessage (mkSimpleDecorated doc) ErrorWithoutFlag hints

mkDecoratedDiagnostic :: DiagnosticReason -> [CSlashHint] -> [SDoc] -> DiagnosticMessage
mkDecoratedDiagnostic rea hints docs = DiagnosticMessage (mkDecorated docs) rea hints

mkDecoratedError :: [CSlashHint] -> [SDoc] -> DiagnosticMessage
mkDecoratedError hints docs = DiagnosticMessage (mkDecorated docs) ErrorWithoutFlag hints

data DiagnosticReason
  = WarningWithoutFlag
  | WarningWithFlags !(NE.NonEmpty WarningFlag)
  | WarningWithCategory !WarningCategory
  | ErrorWithoutFlag
  deriving (Eq, Show)

newtype ResolvedDiagnosticReason
          = ResolvedDiagnosticReason { resolvedDiagnosticReason :: DiagnosticReason }

pattern WarningWithFlag :: WarningFlag -> DiagnosticReason
pattern WarningWithFlag w = WarningWithFlags (w :| [])

instance Outputable DiagnosticReason where
  ppr = \case
    WarningWithoutFlag  -> text "WarningWithoutFlag"
    WarningWithFlags wf -> text ("WarningWithFlags " ++ show wf)
    WarningWithCategory cat -> text "WarningWithCategory" <+> ppr cat
    ErrorWithoutFlag    -> text "ErrorWithoutFlag"

instance Outputable ResolvedDiagnosticReason where
  ppr = ppr . resolvedDiagnosticReason

data MsgEnvelope e = MsgEnvelope
   { errMsgSpan        :: SrcSpan
   , errMsgContext     :: NamePprCtx
   , errMsgDiagnostic  :: e
   , errMsgSeverity    :: Severity
   , errMsgReason      :: ResolvedDiagnosticReason
   } deriving (Functor, Foldable, Traversable)

data MessageClass
  = MCOutput
  | MCFatal
  | MCInteractive
  | MCDump
  | MCInfo
  | MCDiagnostic Severity ResolvedDiagnosticReason (Maybe DiagnosticCode)

data Severity
  = SevIgnore
  | SevWarning
  | SevError
  deriving (Eq, Ord, Show)

instance Outputable Severity where
  ppr = \case
    SevIgnore  -> text "SevIgnore"
    SevWarning -> text "SevWarning"
    SevError   -> text "SevError"

instance Show (MsgEnvelope DiagnosticMessage) where
    show = showMsgEnvelope

showMsgEnvelope :: forall a . Diagnostic a => MsgEnvelope a -> String
showMsgEnvelope err =
  renderWithContext defaultSDocContext (vcat (unDecorated . (diagnosticMessage (defaultDiagnosticOpts @a)) $ errMsgDiagnostic err))

pprMessageBag :: Bag SDoc -> SDoc
pprMessageBag msgs = vcat (punctuate blankLine (bagToList msgs))

mkLocMessage
  :: MessageClass                       
  -> SrcSpan                            
  -> SDoc                               
  -> SDoc
mkLocMessage = mkLocMessageWarningGroups True

mkLocMessageWarningGroups
  :: Bool                               
  -> MessageClass                       
  -> SrcSpan                            
  -> SDoc                               
  -> SDoc
mkLocMessageWarningGroups show_warn_groups msg_class locn msg
    = sdocOption sdocColScheme $ \col_scheme ->
      let locn' = sdocOption sdocErrorSpans $ \case
                     True  -> ppr locn
                     False -> ppr (srcSpanStart locn)

          msg_colour = getMessageClassColour msg_class col_scheme
          col = coloured msg_colour . text

          msg_title = coloured msg_colour $
            case msg_class of
              MCDiagnostic SevError   _ _ -> text "error"
              MCDiagnostic SevWarning _ _ -> text "warning"
              MCFatal                     -> text "fatal"
              _                           -> empty

          warning_flag_doc =
            case msg_class of
              MCDiagnostic sev reason _code
                | Just msg <- flag_msg sev (resolvedDiagnosticReason reason)
                  -> brackets msg
              _   -> empty

          ppr_with_hyperlink code =
            sdocOption (\ ctx -> sdocPrintErrIndexLinks ctx) $
              \ use_hyperlinks ->
                 if use_hyperlinks
                 then ppr $ LinkedDiagCode code
                 else ppr code

          code_doc =
            case msg_class of
              MCDiagnostic _ _ (Just code) -> brackets (ppr_with_hyperlink code)
              _                            -> empty

          flag_msg :: Severity -> DiagnosticReason -> Maybe SDoc
          flag_msg SevIgnore _                 = Nothing
          flag_msg SevError WarningWithoutFlag = Just (col "-Werror")
          flag_msg SevError (WarningWithFlags (wflag :| _)) =
            let name = NE.head (warnFlagNames wflag) in
            Just $ col ("-W" ++ name) <+> warn_flag_grp (smallestWarningGroups wflag)
                                      <> comma
                                      <+> col ("Werror=" ++ name)
          flag_msg SevError   (WarningWithCategory cat) =
            Just $ coloured msg_colour (text "-W" <> ppr cat)
                       <+> warn_flag_grp smallestWarningGroupsForCategory
                       <> comma
                       <+> coloured msg_colour (text "-Werror=" <> ppr cat)
          flag_msg SevError   ErrorWithoutFlag   = Nothing
          flag_msg SevWarning WarningWithoutFlag = Nothing
          flag_msg SevWarning (WarningWithFlags (wflag :| _)) =
            let name = NE.head (warnFlagNames wflag) in
            Just (col ("-W" ++ name) <+> warn_flag_grp (smallestWarningGroups wflag))
          flag_msg SevWarning (WarningWithCategory cat) =
            Just (coloured msg_colour (text "-W" <> ppr cat)
                      <+> warn_flag_grp smallestWarningGroupsForCategory)
          flag_msg SevWarning ErrorWithoutFlag =
            pprPanic "SevWarning with ErrorWithoutFlag" $
              vcat [ text "locn:" <+> ppr locn
                   , text "msg:" <+> ppr msg ]

          warn_flag_grp groups
              | show_warn_groups, not (null groups)
                          = text $ "(in " ++ intercalate ", " (map (("-W"++) . warningGroupName) groups) ++ ")"
              | otherwise = empty

          header = locn' <> colon <+>
                   msg_title <> colon <+>
                   code_doc <+> warning_flag_doc

      in coloured (Col.sMessage col_scheme)
                  (hang (coloured (Col.sHeader col_scheme) header) 4
                        msg)

getMessageClassColour :: MessageClass -> Col.Scheme -> Col.PprColour
getMessageClassColour (MCDiagnostic SevError _reason _code)   = Col.sError
getMessageClassColour (MCDiagnostic SevWarning _reason _code) = Col.sWarning
getMessageClassColour MCFatal                                 = Col.sFatal
getMessageClassColour _                                       = const mempty

getCaretDiagnostic :: MessageClass -> SrcSpan -> IO SDoc
getCaretDiagnostic _ (UnhelpfulSpan _) = pure empty
getCaretDiagnostic msg_class (RealSrcSpan span _) =
  caretDiagnostic <$> getSrcLine (srcSpanFile span) row
  where
    getSrcLine fn i =
      getLine i (unpackFS fn)
        `catchException` \(_ :: IOError) ->
          pure Nothing

    getLine i fn = do
      content <- hGetStringBuffer fn
      case atLine i content of
        Just at_line -> pure $
          case lines (fix <$> lexemeToString at_line (len at_line)) of
            srcLine : _ -> Just srcLine
            _           -> Nothing
        _ -> pure Nothing

    fix '\0' = '\xfffd'
    fix c    = c

    row = srcSpanStartLine span
    rowStr = show row
    multiline = row /= srcSpanEndLine span

    caretDiagnostic Nothing = empty
    caretDiagnostic (Just srcLineWithNewline) =
      sdocOption sdocColScheme$ \col_scheme ->
      let sevColour = getMessageClassColour msg_class col_scheme
          marginColour = Col.sMargin col_scheme
      in
      coloured marginColour (text marginSpace) <>
      text ("\n") <>
      coloured marginColour (text marginRow) <>
      text (" " ++ srcLinePre) <>
      coloured sevColour (text srcLineSpan) <>
      text (srcLinePost ++ "\n") <>
      coloured marginColour (text marginSpace) <>
      coloured sevColour (text (" " ++ caretLine))

      where
        expandTabs tabWidth i s =
          case s of
            ""        -> ""
            '\t' : cs -> replicate effectiveWidth ' ' ++
                         expandTabs tabWidth (i + effectiveWidth) cs
            c    : cs -> c : expandTabs tabWidth (i + 1) cs
          where effectiveWidth = tabWidth - i `mod` tabWidth

        srcLine = filter (/= '\n') (expandTabs 8 0 srcLineWithNewline)

        start = srcSpanStartCol span - 1
        end | multiline = length srcLine
            | otherwise = srcSpanEndCol span - 1
        width = max 1 (end - start)

        marginWidth = length rowStr
        marginSpace = replicate marginWidth ' ' ++ " |"
        marginRow   = rowStr ++ " |"

        (srcLinePre,  srcLineRest) = splitAt start srcLine
        (srcLineSpan, srcLinePost) = splitAt width srcLineRest

        caretEllipsis | multiline = "..."
                      | otherwise = ""
        caretLine = replicate start ' ' ++ replicate width '^' ++ caretEllipsis

isIntrinsicErrorMessage :: Diagnostic e => MsgEnvelope e -> Bool
isIntrinsicErrorMessage = (==) ErrorWithoutFlag . resolvedDiagnosticReason . errMsgReason

isWarningMessage :: Diagnostic e => MsgEnvelope e -> Bool
isWarningMessage = not . isIntrinsicErrorMessage

errorsFound :: Diagnostic e => Messages e -> Bool
errorsFound (Messages msgs) = any isIntrinsicErrorMessage msgs

isExtrinsicErrorMessage :: MsgEnvelope e -> Bool
isExtrinsicErrorMessage = (==) SevError . errMsgSeverity

errorsOrFatalWarningsFound :: Messages e -> Bool
errorsOrFatalWarningsFound (Messages msgs) = any isExtrinsicErrorMessage msgs

getWarningMessages :: Diagnostic e => Messages e -> Bag (MsgEnvelope e)
getWarningMessages (Messages xs) = fst $ partitionBag isWarningMessage xs

getErrorMessages :: Diagnostic e => Messages e -> Bag (MsgEnvelope e)
getErrorMessages (Messages xs) = fst $ partitionBag isIntrinsicErrorMessage xs

partitionMessages :: Diagnostic e => Messages e -> (Messages e, Messages e)
partitionMessages (Messages xs) = bimap Messages Messages (partitionBag isWarningMessage xs)

data DiagnosticCode =
  DiagnosticCode
    { diagnosticCodeNameSpace :: String
    , diagnosticCodeNumber    :: Natural
    }
  deriving ( Eq, Ord )

instance Show DiagnosticCode where
  show (DiagnosticCode prefix c) =
    prefix ++ "-" ++ printf "%05d" c

instance Outputable DiagnosticCode where
  ppr code = text (show code)

newtype LinkedDiagCode = LinkedDiagCode DiagnosticCode

instance Outputable LinkedDiagCode where
  ppr (LinkedDiagCode d@DiagnosticCode{}) = linkEscapeCode d

linkEscapeCode :: DiagnosticCode -> SDoc
linkEscapeCode d = text "\ESC]8;;" <> hfErrorLink d 
                   <> text "\ESC\\" <> ppr d <> text "\ESC]8;;\ESC\\"

hfErrorLink :: DiagnosticCode -> SDoc
hfErrorLink errorCode = text "https://errors.haskell.org/messages/" <> ppr errorCode

