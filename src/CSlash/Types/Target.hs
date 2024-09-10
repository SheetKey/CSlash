module CSlash.Types.Target where

import Prelude hiding ((<>))

import CSlash.Driver.Phases ( Phase )
import CSlash.Unit
import CSlash.Data.StringBuffer ( StringBuffer )
import CSlash.Utils.Outputable

import Data.Time

data Target = Target
  { targetId :: !TargetId
  , targetAllowObjCode :: !Bool
  , targetUnitId :: !UnitId
  , targetContext :: !(Maybe (InputFileBuffer, UTCTime))
  }

data TargetId
  = TargetModule !ModuleName
  | TargetFile !FilePath !(Maybe Phase)
  deriving Eq

type InputFileBuffer = StringBuffer

pprTarget :: Target -> SDoc
pprTarget Target { targetUnitId = uid, targetId = id, targetAllowObjCode = obj } =
  (if obj then empty else char '*') <> ppr uid <> colon <> pprTargetId id

instance Outputable Target where
  ppr = pprTarget

pprTargetId :: TargetId -> SDoc
pprTargetId (TargetModule m) = ppr m
pprTargetId (TargetFile f _) = text f

instance Outputable TargetId where
  ppr = pprTargetId
