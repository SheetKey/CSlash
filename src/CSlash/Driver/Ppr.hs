module CSlash.Driver.Ppr where

import CSlash.Driver.DynFlags
import CSlash.Unit.State

import CSlash.Utils.Outputable
import CSlash.Utils.Ppr       ( Mode(..) )

import System.IO ( Handle )

showSDoc :: DynFlags -> SDoc -> String
showSDoc dflags sdoc = renderWithContext (initSDocContext dflags defaultUserStyle) sdoc

showPpr :: Outputable a => DynFlags -> a -> String
showPpr dflags thing = showSDoc dflags (ppr thing)

showSDocForUser :: DynFlags -> UnitState -> NamePprCtx -> SDoc -> String
showSDocForUser dflags unit_state name_ppr_ctx doc
  = renderWithContext (initSDocContext dflags sty) doc'
  where
    sty = mkUserStyle name_ppr_ctx AllTheWay
    doc' = pprWithUnitState unit_state doc

printForUser :: DynFlags -> Handle -> NamePprCtx -> Depth -> SDoc -> IO ()
printForUser dflags handle name_ppr_ctx depth doc
  = printSDocLn ctx (PageMode False) handle doc
  where
    ctx = initSDocContext dflags (mkUserStyle name_ppr_ctx depth)
