module CSlash.Unit.Module.ModSummary where

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
