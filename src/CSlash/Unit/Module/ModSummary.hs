module CSlash.Unit.Module.ModSummary where

import CSlash.Cs

import CSlash.Unit.Types
import CSlash.Unit.Module

import GHC.Types.SourceFile ( HscSource(..), hscSourceString )
import GHC.Types.SrcLoc
import GHC.Types.Target
import GHC.Types.PkgQual

import GHC.Data.Maybe
import GHC.Data.StringBuffer ( StringBuffer )

import GHC.Utils.Fingerprint
import GHC.Utils.Outputable

import Data.Time

data ModSummary = ModSummary
  { ms_mod :: Module
  , ms_csl_src :: CslSource
  , ms_location :: ModLocation
  , ms_cs_hash :: Fingerprint
  , ms_obj_date :: Maybe UTCTime
  , ms_dyn_obj_date :: !(Maybe UTCTime)
  , ms_textual_imps :: [(PkgQual, Located ModuleName)]
  , ms_cs_prim_import :: !Bool
  , ms_parsed_mod :: Maybe CsParsedModule
  }
