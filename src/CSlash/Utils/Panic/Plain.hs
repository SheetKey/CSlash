{-# LANGUAGE LambdaCase #-}

module CSlash.Utils.Panic.Plain where

import CSlash.Stack
import CSlash.Utils.Constants
import CSlash.Utils.Exception as Exception
import CSlash.Version

data PlainCsException
  = PlainSignal Int
  | PlainUsageError String
  | PlainCmdLineError String
  | PlainPanic String
  | PlainSorry String
  | PlainInstallationError String
  | PlainProgramError String

instance Exception PlainCsException

instance Show PlainCsException where
  showsPrec _ e = showPlainCsException e

short_usage :: String
short_usage = "Usage: For basic information, try the `--help' option."

showPlainCsException :: PlainCsException -> ShowS
showPlainCsException =
  \case
    PlainSignal n -> showString "signal: " . shows n
    PlainUsageError str -> showString str . showChar '\n' . showString short_usage
    PlainCmdLineError str -> showString str
    PlainPanic s -> panicMsg (showString s)
    PlainSorry s -> sorryMsg (showString s)
    PlainInstallationError str -> showString str
    PlainProgramError str -> showString str
  where
    sorryMsg :: ShowS -> ShowS
    sorryMsg s =
        showString "sorry! (unimplemented feature or known bug)\n"
      . showString ("  CSlash version " ++ cProjectVersion ++ ":\n\t")
      . s . showString "\n"
    panicMsg :: ShowS -> ShowS
    panicMsg s =
        showString "panic! (then 'impossible' happened)\n"
      . showString ("  CSlash version " ++ cProjectVersion ++ ":\n\t")
      . s . showString "\n"

assertPanic' :: HasCallStack => a
assertPanic' =
  let doc = unlines $ fmap ("  "++) $ lines (prettyCallStack callStack)
  in Exception.throw (Exception.AssertionFailed
                       ("ASSERT failed!\n"
                       ++ withFrozenCallStack doc))

assert :: HasCallStack => Bool -> a -> a
{-# INLINE assert #-}
assert cond a =
  if debugIsOn && not cond
  then withFrozenCallStack assertPanic'
  else a
