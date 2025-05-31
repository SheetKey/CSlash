module CSlash.Utils.Trace where

import CSlash.Utils.Outputable
import CSlash.Utils.Exception
import CSlash.Utils.Panic
import CSlash.Utils.GlobalVars
import CSlash.Utils.Constants
import CSlash.Stack

import Debug.Trace (trace)
import Control.Monad.IO.Class

pprTrace :: String -> SDoc -> a -> a
pprTrace str doc x
  --  | unsafeHasNoDebugOutput = x
  | otherwise = pprDebugAndThen traceSDocContext trace (text str) doc x

warnPprTrace :: HasCallStack => Bool -> String -> SDoc -> a -> a
warnPprTrace _ _ _ x | not debugIsOn = x
warnPprTrace _ _ _ x | unsafeHasNoDebugOutput = x
warnPprTrace False _ _ x = x
warnPprTrace True s msg x = pprDebugAndThen traceSDocContext trace (text "WARNING:")
                            (text s $$ msg $$ withFrozenCallStack traceCallStackDoc) x

traceCallStackDoc :: HasCallStack => SDoc
traceCallStackDoc = hang (text "Call stack:")
                         4 (vcat $ map text $ lines (prettyCallStack callStack))
