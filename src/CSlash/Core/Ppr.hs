module CSlash.Core.Ppr where

import CSlash.Core
import CSlash.Types.Fixity (LexicalFixity(..))
import CSlash.Types.Name( pprInfixName, pprPrefixName )
import CSlash.Types.Var
import CSlash.Types.Id
import CSlash.Types.Id.Info
import CSlash.Core.DataCon
import CSlash.Core.TyCon
import CSlash.Core.Type.Ppr
import CSlash.Types.Basic
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Types.SrcLoc ( pprUserRealSpan )
import CSlash.Types.Tickish

pprCoreExpr :: OutputableBndr b => Expr b -> SDoc
pprCoreExpr = undefined

instance OutputableBndr b => Outputable (Expr b) where
  ppr expr = pprCoreExpr expr

instance OutputableBndr Var where
  pprBndr = undefined
  pprInfixOcc = undefined
  pprPrefixOcc = undefined
  bndrIsJoin_maybe = undefined
