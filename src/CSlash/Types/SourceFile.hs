module CSlash.Types.SourceFile where

import CSlash.Utils.Binary
import CSlash.Unit.Types

data CslSource = CsSrcFile
  deriving (Eq, Ord, Show)

instance Binary CslSource where
  put_ bh CsSrcFile = putByte bh 0
  get bh = do
    h <- getByte bh
    case h of
      _ -> return CsSrcFile
