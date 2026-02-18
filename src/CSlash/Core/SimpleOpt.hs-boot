module CSlash.Core.SimpleOpt where

import CSlash.Core
import CSlash.Utils.Misc ( HasDebugCallStack )

data SimpleOpts

simpleOptExpr :: HasDebugCallStack => SimpleOpts -> CoreExpr -> CoreExpr