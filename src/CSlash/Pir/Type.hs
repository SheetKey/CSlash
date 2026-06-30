module CSlash.Pir.Type where

import CSlash.Platform
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Data.Word
import Data.Int

-----------------------------------------------------------------------------
--              CmmType
-----------------------------------------------------------------------------

data PirType = PirType
  deriving Show

instance Outputable PirType
