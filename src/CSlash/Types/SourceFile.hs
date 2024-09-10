module CSlash.Types.SourceFile where

import CSlash.Utils.Binary
import CSlash.Unit.Types

data CsSource = CsSrcFile
  deriving (Eq, Ord, Show)

instance Binary CsSource where
  put_ bh CsSrcFile = putByte bh 0
  get bh = do
    h <- getByte bh
    case h of
      _ -> return CsSrcFile

csSourceString :: CsSource -> String
csSourceString CsSrcFile = ""
