module CSlash.Types.CompleteMatch where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Core.Type.Rep
import CSlash.Types.Unique.DSet
import CSlash.Core.ConLike
import CSlash.Core.TyCon
-- import GHC.Core.Type ( splitTyConApp_maybe )
import CSlash.Utils.Outputable

data CompleteMatch = CompleteMatch
  { cmConLikes :: UniqDSet (ConLike Zk)
  , cmResultTyCon :: Maybe (TyCon Zk)
  }

instance Outputable CompleteMatch where
  ppr (CompleteMatch cls mty) = case mty of
    Nothing -> ppr cls
    Just ty -> ppr cls <> text "@" <> parens (ppr ty)

type CompleteMatches = [CompleteMatch]
type DsCompleteMatches = CompleteMatches
