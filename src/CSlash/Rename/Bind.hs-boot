{-# LANGUAGE ConstraintKinds #-}

module CSlash.Rename.Bind where

import CSlash.Cs
import CSlash.Rename.CsKind (BindKVs)
import CSlash.Types.Name.Set ( FreeVars )
import CSlash.Tc.Types
import CSlash.Utils.Outputable  ( Outputable )

type RnMatchAnnoBody body
  = ( Anno [LocatedA (Match Rn (LocatedA (body Rn)))] ~ SrcSpanAnnL
    , Anno [LocatedA (Match Ps (LocatedA (body Ps)))] ~ SrcSpanAnnL
    , Anno (Match Rn (LocatedA (body Rn))) ~ SrcSpanAnnA
    , Anno (Match Ps (LocatedA (body Ps))) ~ SrcSpanAnnA
    , Anno (GRHS Rn (LocatedA (body Rn))) ~ EpAnnCO
    , Anno (GRHS Ps (LocatedA (body Ps))) ~ EpAnnCO
    , Outputable (body Ps)
    )

rnMatchGroup
  :: RnMatchAnnoBody body
  => BindKVs
  -> CsMatchContextRn
  -> (LocatedA (body Ps) -> RnM (LocatedA (body Rn), FreeVars))
  -> MatchGroup Ps (LocatedA (body Ps))
  -> RnM (MatchGroup Rn (LocatedA (body Rn)), FreeVars)
