module CSlash.Types.CompleteMatch where

import Prelude hiding ((<>))

import CSlash.Core.Type.Rep
import CSlash.Types.Unique.DSet
import CSlash.Core.ConLike
import CSlash.Core.TyCon
-- import GHC.Core.Type ( splitTyConApp_maybe )
import CSlash.Utils.Outputable
import CSlash.Types.Var (TyVar, KiVar)

data CompleteMatch = CompleteMatch
  { cmConLikes :: UniqDSet (ConLike (TyVar KiVar) KiVar)
  , cmResultTyCon :: Maybe (TyCon (TyVar KiVar) KiVar)
  }

instance Outputable CompleteMatch where
  ppr (CompleteMatch cls mty) = case mty of
    Nothing -> ppr cls
    Just ty -> ppr cls <> text "@" <> parens (ppr ty)

type CompleteMatches = [CompleteMatch]
