module CSlash.Pir.UniqueRenamer
  ( module CSlash.Pir.UniqueRenamer
  , module CSlash.Types.Unique.DSM
  ) where

import CSlash.Utils.Monad.State.Strict
import Data.Tuple (swap)
import GHC.Word
import CSlash.Pir
import CSlash.Pir.PLabel
import CSlash.Pir.Dataflow.Block
import CSlash.Pir.Dataflow.Graph
import CSlash.Pir.Dataflow.Label
-- import GHC.Cmm.Switch
import CSlash.Types.Unique
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.DFM
import CSlash.Utils.Outputable as Outputable
import CSlash.Types.Var.Id
import CSlash.Types.Unique.DSM
import CSlash.Types.Name hiding (varName)
import CSlash.Types.Var
-- import GHC.Types.IPE

data DetUniqFM = DetUniqFM
  { mapping :: !(UniqFM Unique Unique)
  , supply :: !Word64
  }

instance Outputable DetUniqFM where
  ppr (DetUniqFM mapping supply) = ppr mapping $$ text "supply:" Outputable.<> ppr supply

emptyDetUFM :: DetUniqFM
emptyDetUFM = DetUniqFM
  { mapping = emptyUFM
  , supply = 54
  }
