{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module CSlash.Cs.Pat
  ( Pat(..), LPat

  , patNeedsParens

  , pprParendLPat
  ) where

import CSlash.Language.Syntax.Extension
import CSlash.Language.Syntax.Pat
import CSlash.Cs.Extension
import CSlash.Cs.Lit
import CSlash.Cs.Type
import CSlash.Types.Basic
import CSlash.Types.SrcLoc
import CSlash.Parser.Annotation
import CSlash.Utils.Outputable

instance Outputable (CsTyPat p) => Outputable (CsConPatTyArg p) where
  ppr (CsConPatTyArg _ ty) = ppr ty

instance OutputableBndrId p => Outputable (Pat (CsPass p)) where
  ppr = pprPat

pprPatBndr :: OutputableBndr name => name -> SDoc
pprPatBndr var
  = getPprDebug $ \case
  True -> parens (pprBndr LambdaBind var)
  False -> pprPrefixOcc var

pprParendLPat :: (OutputableBndrId p) => PprPrec -> LPat (CsPass p) -> SDoc
pprParendLPat p = pprParendPat p . unLoc

pprParendPat
  :: (OutputableBndrId p)
  => PprPrec -> Pat (CsPass p) -> SDoc
pprParendPat p pat = 
  if patNeedsParens p pat
  then parens (pprPat pat)
  else pprPat pat

patNeedsParens :: IsPass p => PprPrec -> Pat (CsPass p) -> Bool
patNeedsParens p = go
  where
    go :: IsPass q => Pat (CsPass q) -> Bool
    go (WildPat{}) = False
    go (VarPat{}) = False
    go (TuplePat{}) = p >= appPrec
    go (SumPat{}) = False
    go (LitPat _ l) = csLitNeedsParens p l
    go (SigPat{}) = p >= sigPrec

pprPat :: (OutputableBndrId p) => Pat (CsPass p) -> SDoc
pprPat (WildPat{}) = char '_'
pprPat (VarPat _ lvar) = pprPatBndr (unLoc lvar)
pprPat (TuplePat _ pats) = parens (pprWithCommas ppr pats)
pprPat (SumPat _ pat alt arity) = parens (pprAlternative ppr pat alt arity)
pprPat (LitPat _ s) = ppr s
pprPat (SigPat _ pat ty) = ppr pat <+> colon <+> ppr ty

type instance Anno (Pat (CsPass p)) = SrcSpanAnnA
