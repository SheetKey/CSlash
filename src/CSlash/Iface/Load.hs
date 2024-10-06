module CSlash.Iface.Load where

import CSlash.Platform.Profile

import Prelude hiding ((<>))

-- import {-# SOURCE #-} GHC.IfaceToCore
--    ( tcIfaceDecls, tcIfaceRules, tcIfaceInst, tcIfaceFamInst
--    , tcIfaceAnnotations, tcIfaceCompleteMatches )

import CSlash.Driver.Config.Finder
import CSlash.Driver.Env
import CSlash.Driver.Errors.Types
import CSlash.Driver.DynFlags
-- import GHC.Driver.Hooks
-- import GHC.Driver.Plugins

import CSlash.Iface.Syntax
-- import GHC.Iface.Ext.Fields
import CSlash.Iface.Binary
-- import GHC.Iface.Rename
-- import GHC.Iface.Env
-- import GHC.Iface.Errors as Iface_Errors

-- import GHC.Tc.Errors.Types
-- import GHC.Tc.Utils.Monad

import CSlash.Utils.Binary   ( BinData(..) )
import CSlash.Utils.Error
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.Logger

import CSlash.Settings.Constants

import CSlash.Builtin.Names
import CSlash.Builtin.Utils
-- import GHC.Builtin.PrimOps    ( allThePrimOps, primOpFixity, primOpOcc )

-- import GHC.Core.Rules
import CSlash.Core.TyCon
-- import GHC.Core.InstEnv
-- import GHC.Core.FamInstEnv

-- import CSlash.Types.Id.Make      ( seqId )
-- import GHC.Types.Annotations
import CSlash.Types.Name
import CSlash.Types.Name.Cache
import CSlash.Types.Name.Env
import CSlash.Types.Avail
import CSlash.Types.Fixity
import CSlash.Types.Fixity.Env
import CSlash.Types.SourceError
import CSlash.Types.SourceText
import CSlash.Types.SourceFile
-- import GHC.Types.SafeHaskell
import CSlash.Types.TypeEnv
import CSlash.Types.Unique.DSet
import CSlash.Types.SrcLoc
import CSlash.Types.TyThing
import CSlash.Types.PkgQual

import CSlash.Unit.External
import CSlash.Unit.Module
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.Deps
import CSlash.Unit.State
import CSlash.Unit.Home
import CSlash.Unit.Home.ModInfo
import CSlash.Unit.Finder
import CSlash.Unit.Env

import CSlash.Data.Maybe

import Control.Monad
import Data.Map ( toList )
import System.FilePath
import System.Directory
import CSlash.Driver.Env.KnotVars
-- import GHC.Iface.Errors.Types

{- *********************************************************************
*                                                                      *
                Printing interfaces
*                                                                      *
********************************************************************* -}

showIface :: Logger -> DynFlags -> UnitState -> NameCache -> FilePath -> IO ()
showIface logger dflags unit_state name_cache filename = do
  let profile = targetProfile dflags
      printer = logMsg logger MCOutput noSrcSpan . withPprStyle defaultDumpStyle

  iface <- readBinIface profile name_cache IgnoreHiWay (TraceBinIFace printer) filename

  let qualifyImportedNames mod _
        | mod == mi_module iface = NameUnqual
        | otherwise = NameNotInScope1
      name_ppr_ctx = QueryQualify qualifyImportedNames neverQualifyModules
                                  neverQualifyPackages alwaysPrintPromTick

  logMsg logger MCDump noSrcSpan
    $ withPprStyle (mkDumpStyle name_ppr_ctx)
    $ pprModIface unit_state iface

pprModIface :: UnitState -> ModIface -> SDoc
pprModIface unit_state iface@ModIface{ mi_final_exts = exts }
 = vcat [ text "interface"
                <+> ppr (mi_module iface) <+> pp_hsc_src (mi_cs_src iface)
                <+> (if mi_pc iface then text "[pc]" else Outputable.empty)
                <+> integer hiVersion
        , nest 2 (text "interface hash:" <+> ppr (mi_iface_hash exts))
        , nest 2 (text "ABI hash:" <+> ppr (mi_mod_hash exts))
        , nest 2 (text "export-list hash:" <+> ppr (mi_exp_hash exts))
        , nest 2 (text "flag hash:" <+> ppr (mi_flag_hash exts))
        , nest 2 (text "opt_hash:" <+> ppr (mi_opt_hash exts))
        , nest 2 (text "pc_hash:" <+> ppr (mi_pc_hash exts))
        , nest 2 (text "src_hash:" <+> ppr (mi_src_hash iface))
        , nest 2 (text "where")
        , text "exports:"
        , nest 2 (vcat (map pprExport (mi_exports iface)))
        , pprDeps unit_state (mi_deps iface)
        , vcat (map pprUsage (mi_usages iface))
        , vcat (map pprIfaceAnnotation (mi_anns iface))
        , pprFixities (mi_fixities iface)
        , vcat [ppr ver $$ nest 2 (ppr decl) | (ver,decl) <- mi_decls iface]
        , case mi_extra_decls iface of
            Nothing -> empty
            Just eds -> text "extra decls:"
                          $$ nest 2 (vcat ([ppr bs | bs <- eds]))
        , vcat (map ppr (mi_complete_matches iface))
        ]
  where
    pp_hsc_src CsSrcFile  = Outputable.empty

pprExport :: IfaceExport -> SDoc
pprExport (Avail n) = ppr n
pprExport (AvailTC _ []) = Outputable.empty
pprExport avail@(AvailTC n _) =
  ppr n <> mark <> pp_export (availSubordinateNames avail)
  where
    mark | availExportsDecl avail = Outputable.empty
         | otherwise = vbar

    pp_export [] = Outputable.empty
    pp_export names = braces (hsep (map ppr names))

pprUsage :: Usage -> SDoc
pprUsage usage@UsagePackageModule{} = pprUsageImport usage usg_mod
pprUsage usage@UsageHomeModule{}
  = pprUsageImport usage (\u -> mkModule (usg_unit_id u) (usg_mod_name u)) $$
    nest 2 ( maybe Outputable.empty (\v -> text "exports: " <> ppr v) (usg_exports usage) $$
             vcat [ ppr n <+> ppr v | (n, v) <- usg_entities usage ]
           )

pprUsageImport :: Outputable a => Usage -> (Usage -> a) -> SDoc
pprUsageImport usage usg_mod'
  = hsep [ text "import"
         , ppr (usg_mod' usage)
         , ppr (usg_mod_hash usage)
         ]

pprFixities :: [(OccName, Fixity)] -> SDoc
pprFixities [] = Outputable.empty
pprFixities fixes = text "fixities" <+> pprWithCommas pprFix fixes
  where
    pprFix (occ, fix) = ppr fix <+> ppr occ

pprIfaceAnnotation :: IfaceAnnotation -> SDoc
pprIfaceAnnotation = undefined
