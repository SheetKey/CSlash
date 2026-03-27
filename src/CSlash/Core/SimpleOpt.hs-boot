module CSlash.Core.SimpleOpt where

import CSlash.Core
import {-# SOURCE #-} CSlash.Core.Unfold
import CSlash.Utils.Misc ( HasDebugCallStack )

data SimpleOpts

so_uf_opts :: SimpleOpts -> UnfoldingOpts

simpleOptExpr :: HasDebugCallStack => SimpleOpts -> CoreExpr -> CoreExpr