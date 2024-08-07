{-# LANGUAGE LambdaCase #-}

module CSlash.Utils.Panic
  ( module CSlash.Utils.Panic
  , module CSlash.Utils.Panic.Plain
  ) where

import CSlash.Stack

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic.Plain
import CSlash.Utils.Constants

import CSlash.Utils.Exception as Exception

import Data.Typeable ( cast )

data CsException
  = Signal Int
  | UsageError String
  | CmdLineError String
  | Panic String
  | PprPanic String SDoc
  | Sorry String
  | PprSorry String SDoc
  | InstallationError String
  | ProgramError String
  | PprProgramError String SDoc

instance Exception CsException where
  fromException (SomeException e)
    | Just ge <- cast e = Just ge
    | Just pge <- cast e = Just $
      case pge of
        PlainSignal n -> Signal n
        PlainUsageError str -> UsageError str
        PlainCmdLineError str -> CmdLineError str
        PlainPanic str -> Panic str
        PlainSorry str -> Sorry str
        PlainInstallationError str -> InstallationError str
        PlainProgramError str -> ProgramError str
    | otherwise = Nothing
  displayException exc = showCsExceptionUnsafe exc ""

instance Show CsException where
  showsPrec _ e = showCsExceptionUnsafe e

showCsExceptionUnsafe :: CsException -> ShowS
showCsExceptionUnsafe = showCsException defaultSDocContext

showCsException :: SDocContext -> CsException -> ShowS
showCsException ctx = showPlainCsException . \case
  Signal n -> PlainSignal n
  UsageError str -> PlainUsageError str
  CmdLineError str -> PlainCmdLineError str
  Panic str -> PlainPanic str
  Sorry str -> PlainSorry str
  InstallationError str -> PlainInstallationError str
  ProgramError str -> PlainProgramError str

  PprPanic str sdoc -> PlainPanic $
      concat [str, "\n\n", renderWithContext ctx sdoc]
  PprSorry str sdoc -> PlainProgramError $
      concat [str, "\n\n", renderWithContext ctx sdoc]
  PprProgramError str sdoc -> PlainProgramError $
      concat [str, "\n\n", renderWithContext ctx sdoc]

throwCsException :: CsException -> a
throwCsException = Exception.throw

throwCsExceptionIO :: CsException -> IO a
throwCsExceptionIO = Exception.throwIO

pprPanic :: HasCallStack => String -> SDoc -> a
pprPanic s doc = panicDoc s (doc $$ callStackDoc)

panicDoc :: String -> SDoc -> a
panicDoc x doc = throwCsException (PprPanic x doc)

callStackDoc :: HasCallStack => SDoc
callStackDoc = prettyCallStackDoc callStack

prettyCallStackDoc :: CallStack -> SDoc
prettyCallStackDoc cs =
  hang (text "Call stack:")
       4 (vcat $ map text $ lines (prettyCallStack cs))

assertPprPanic :: HasCallStack => SDoc -> a
assertPprPanic msg = withFrozenCallStack (pprPanic "ASSERT failed!" msg)

assertPpr :: HasCallStack => Bool -> SDoc -> a -> a
{-# INLINE assertPpr #-}
assertPpr cond msg a =
  if debugIsOn && not cond
  then withFrozenCallStack (assertPprPanic msg)
  else a
