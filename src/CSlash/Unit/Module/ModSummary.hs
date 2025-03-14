module CSlash.Unit.Module.ModSummary where

import Prelude hiding ((<>))

import CSlash.Cs

import CSlash.Driver.DynFlags

import CSlash.Unit.Types
import CSlash.Unit.Module

import CSlash.Types.SourceFile ( CsSource(..), csSourceString )
import CSlash.Types.SrcLoc
-- import CSlash.Types.Target
import CSlash.Types.PkgQual

import CSlash.Data.Maybe
import CSlash.Data.StringBuffer ( StringBuffer )

import CSlash.Utils.Fingerprint
import CSlash.Utils.Outputable

import Data.Time

data ModSummary = ModSummary
  { ms_mod :: Module
  , ms_cs_src :: CsSource
  , ms_location :: ModLocation
  , ms_cs_hash :: Fingerprint
  , ms_obj_date :: Maybe UTCTime
  , ms_dyn_obj_date :: !(Maybe UTCTime)
  , ms_iface_date :: Maybe UTCTime
  , ms_hie_date :: Maybe UTCTime
  , ms_textual_imps :: [(PkgQual, Located ModuleName)]
  , ms_csl_prim_import :: !Bool
  , ms_parsed_mod :: Maybe CsParsedModule
  , ms_cs_file :: FilePath
  , ms_cs_opts :: DynFlags
  , ms_cs_buf :: Maybe StringBuffer
  }

ms_unitid :: ModSummary -> UnitId
ms_unitid = toUnitId . moduleUnit . ms_mod

ms_mod_name :: ModSummary -> ModuleName
ms_mod_name = moduleName . ms_mod

ms_imps :: ModSummary -> [(PkgQual, Located ModuleName)]
ms_imps = ms_textual_imps

msCsFilePath :: ModSummary -> FilePath
msCsFilePath ms = expectJust "msCsFilePath" (ml_cs_file (ms_location ms))

msDynHiFilePath :: ModSummary -> FilePath
msDynHiFilePath ms = ml_dyn_hi_file (ms_location ms)

msHiFilePath :: ModSummary -> FilePath
msHiFilePath ms = ml_hi_file (ms_location ms)

msObjFilePath :: ModSummary -> FilePath
msObjFilePath ms = ml_obj_file (ms_location ms)

msDynObjFilePath :: ModSummary -> FilePath
msDynObjFilePath ms = ml_dyn_obj_file (ms_location ms)

msDeps :: ModSummary -> [(PkgQual, Located ModuleName)]
msDeps = ms_imps

instance Outputable ModSummary where
  ppr ms = sep [ text "ModSummary {"
               , nest 3 (sep [ text "ms_cs_hash = " <> text (show (ms_cs_hash ms))
                             , text "ms_mod = " <+> ppr (ms_mod ms)
                               <> text (csSourceString (ms_cs_src ms)) <> comma
                             , text "unit =" <+> ppr (ms_unitid ms)
                             , text "ms_textual_imps =" <+> ppr (ms_textual_imps ms)
                             ])
               , char '}'
               ]
