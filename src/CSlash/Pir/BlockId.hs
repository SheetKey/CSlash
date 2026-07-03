module CSlash.Pir.BlockId where

import CSlash.Pir.PLabel
import CSlash.Data.FastString
import CSlash.Types.Var.Id.Info
import CSlash.Types.Name
import CSlash.Types.Unique
import qualified CSlash.Types.Unique.DSM as DSM

import CSlash.Pir.Dataflow.Label (Label, mkHooplLabel)

type BlockId = Label

mkBlockId :: Unique -> BlockId
mkBlockId unique = mkHooplLabel $ getKey unique

newBlockId :: DSM.MonadGetUnique m => m BlockId
newBlockId = mkBlockId <$> DSM.getUniqueM
