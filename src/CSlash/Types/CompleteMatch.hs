{-# LANGUAGE TypeApplications #-}

module CSlash.Types.CompleteMatch where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Core.Type.Rep
import CSlash.Types.Unique
import CSlash.Types.Unique.DSet
import CSlash.Core.ConLike
import CSlash.Core.TyCon
import CSlash.Core.Type ( splitTyConApp_maybe )
import CSlash.Utils.Outputable
import CSlash.Types.Name

type CompleteMatch = CompleteMatchX Name
type DsCompleteMatch = CompleteMatchX (ConLike Zk)

type CompleteMatches = [CompleteMatch]
type DsCompleteMatches = [DsCompleteMatch]

data CompleteMatchX con = CompleteMatch
  { cmConLikes :: UniqDSet con
  , cmResultTyCon :: Maybe Name
  }
  deriving Eq

mkCompleteMatch :: UniqDSet con -> Maybe Name -> CompleteMatchX con
mkCompleteMatch nms mb_tc = CompleteMatch { cmConLikes = nms, cmResultTyCon = mb_tc }

vanillaCompleteMatch :: UniqDSet con -> CompleteMatchX con
vanillaCompleteMatch nms = mkCompleteMatch nms Nothing

instance Outputable con => Outputable (CompleteMatchX con) where
  ppr (CompleteMatch cls mty) = case mty of
    Nothing -> ppr cls
    Just ty -> ppr cls <> text "@" <> parens (ppr ty)

completeMatchAppliesAtType :: Type Zk -> CompleteMatchX con -> Bool
completeMatchAppliesAtType ty cm = all @Maybe ty_matches (getUnique <$> cmResultTyCon cm)
  where
    ty_matches :: Unique -> Bool
    ty_matches sig_tc
      | Just (tc, _arg_tys) <- splitTyConApp_maybe ty
      , tc `hasKey` sig_tc
      = True
      | otherwise
      = False
