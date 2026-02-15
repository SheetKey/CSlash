module CSlash.Types.CompleteMatch where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Core.Type.Rep
import CSlash.Types.Unique.DSet
import CSlash.Core.ConLike
import CSlash.Core.TyCon
-- import GHC.Core.Type ( splitTyConApp_maybe )
import CSlash.Utils.Outputable
import CSlash.Types.Name

type CompleteMatch = CompleteMatchX Name
type DsCompleteMatch = CompleteMatchX (ConLike Zk)

type CompleteMatches = [CompleteMatch]
type DsCompleteMatches = CompleteMatches

data CompleteMatchX con = CompleteMatch
  { cmConLikes :: UniqDSet con
  , cmResultTyCon :: Maybe Name
  }
  deriving Eq

instance Outputable con => Outputable (CompleteMatchX con) where
  ppr (CompleteMatch cls mty) = case mty of
    Nothing -> ppr cls
    Just ty -> ppr cls <> text "@" <> parens (ppr ty)

