module CSlash.Tc.Gen.Export where

import CSlash.Cs
import CSlash.Builtin.Names
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Utils.Env
    ( TyThing(AConLike, AnId), tcLookupGlobal )
import CSlash.Tc.Utils.TcType
import CSlash.Rename.Module
import CSlash.Rename.Names
import CSlash.Rename.Env
import CSlash.Rename.Unbound ( reportUnboundName )
import CSlash.Utils.Error
import CSlash.Unit.Module
import CSlash.Unit.Module.Imported
import CSlash.Unit.Module.Warnings
import CSlash.Core.TyCon
import CSlash.Utils.Misc (sndOf3, thdOf3)
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Core.ConLike
import CSlash.Data.Maybe
import CSlash.Data.FastString (fsLit)
import CSlash.Driver.Env
import CSlash.Driver.DynFlags
-- import CSlash.Parser.PostProcess ( setRdrNameSpace )

import CSlash.Types.Unique.Map
import CSlash.Types.SrcLoc as SrcLoc
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set
import CSlash.Types.Avail
import CSlash.Types.SourceFile
import CSlash.Types.Id
import CSlash.Types.Id.Info
import CSlash.Types.Name.Reader

import Control.Arrow ( first )
import Control.Monad ( when )
import qualified Data.List.NonEmpty as NE
import Data.Traversable   ( for )
import Data.List ( sortBy )
import qualified Data.Map as Map

rnExports :: Maybe (LocatedL [LIE Ps]) -> RnM (TcGblEnv Tc)
rnExports exports = checkNoErrs $ do
  cs_env <- getTopEnv
  tcg_env <- getGblEnv
  let dflags = cs_dflags cs_env
      TcGblEnv { tcg_mod = this_mod
               , tcg_rdr_env = rdr_env
               , tcg_imports = imports
               , tcg_src = cs_src } = tcg_env
      default_main
        | mainModIs (cs_HUE cs_env) == this_mod
        , Just main_fun <- mainFunIs dflags
        = mkUnqual varName (fsLit main_fun)
        | otherwise
        = main_RDR_Unqual
  has_main <- (not . null) <$> lookupInfoOccRn default_main

  (rn_exports, final_avails) <- checkNoErrs $ exports_from_avail exports rdr_env imports this_mod

  let final_ns = availsToNameSet final_avails

  traceRn "rnExports: Exports:" (ppr final_avails)

  return (tcg_env { tcg_exports = final_avails
                  , tcg_rn_exports = case tcg_rn_exports tcg_env of
                                       Nothing -> Nothing
                                       Just _ -> rn_exports
                  , tcg_dus = tcg_dus tcg_env `plusDU` usesOnly final_ns
                  })

exports_from_avail
  :: Maybe (LocatedL [LIE Ps])
  -> GlobalRdrEnv
  -> ImportAvails
  -> Module
  -> RnM (Maybe [(LIE Rn, Avails)], Avails)
exports_from_avail Nothing rdr_env _ this_mod = do
  panic "addDiagnostic (TcRnMissingExportList $ moduleName this_mod)"
  let avails = map fix_faminst . gresToAvailInfo . filter isLocalGRE . globalRdrEnvElts $ rdr_env
  return (Nothing, avails)
  where
    fix_faminst avail@(AvailTC n ns)
      | availExportsDecl avail
      = avail
      | otherwise
      = AvailTC n (n:ns)
    fix_faminst avail = avail
exports_from_avail (Just (L _ rdr_items)) rdr_env imports this_mod = panic "exports_from_avail"
