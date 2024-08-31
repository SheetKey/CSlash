module CSlash.Unit.Module.Location where

import CSlash.Unit.Types
import CSlash.Utils.Outputable

data ModLocation = ModLocation
  { ml_cs_file :: Maybe FilePath
  , ml_hi_file :: FilePath
  , ml_dyn_hi_file :: FilePath
  , ml_obj_file :: FilePath
  , ml_dyn_obj_file :: FilePath
  , ml_hie_file :: FilePath
  }
  deriving Show

instance Outputable ModLocation where
  ppr = text . show
