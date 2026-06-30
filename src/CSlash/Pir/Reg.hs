module CSlash.Pir.Reg where

import Prelude hiding ((<>))

import CSlash.Platform
import CSlash.Utils.Outputable
import CSlash.Types.Unique
import CSlash.Pir.Type

-----------------------------------------------------------------------------
--              Pir registers
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
--              Local registers
-----------------------------------------------------------------------------

data LocalReg = LocalReg {-# UNPACK #-} !Unique !PirType
  deriving Show

instance Eq LocalReg where
  (LocalReg u1 _) == (LocalReg u2 _) = u1 == u2

instance Outputable LocalReg where
  ppr = pprLocalReg

localRegType :: LocalReg -> PirType
localRegType (LocalReg _ rep) = rep

pprLocalReg :: LocalReg -> SDoc
pprLocalReg (LocalReg uniq rep) =
  char '_' <> pprUnique uniq <> colon <> ppr rep
  where
    pprUnique unique = sdocOption sdocSuppressUniques $ \c ->
      if c then text "_locVar_" else ppr unique
