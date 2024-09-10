module CSlash.Unit.Module.ModDetails where

import CSlash.Types.Avail
import CSlash.Types.CompleteMatch
import CSlash.Types.TypeEnv
-- import GHC.Types.Annotations ( Annotation )

data ModDetails = ModDetails
  { md_exports :: [AvailInfo]
  , md_types :: !TypeEnv
  , md_complete_matches :: [CompleteMatch]
  }
