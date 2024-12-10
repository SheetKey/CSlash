{-# LANGUAGE GeneralisedNewtypeDeriving #-}

module CSlash.Tc.Types.Constraint
  ( module CSlash.Tc.Types.Constraint
  , module CSlash.Tc.Types.CtLocEnv
  ) where

import Prelude hiding ((<>))

-- import GHC.Core.Predicate
import CSlash.Core.Type
-- import GHC.Core.Coercion
-- import GHC.Core.Class
import CSlash.Core.TyCon
import CSlash.Types.Name
import CSlash.Types.Var

import CSlash.Tc.Utils.TcType
-- import GHC.Tc.Types.Evidence
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.CtLocEnv

import CSlash.Core

import CSlash.Core.Type.Ppr
-- import CSlash.Utils.FV
import CSlash.Types.Var.Set
import CSlash.Builtin.Names
import CSlash.Types.Basic
import CSlash.Types.Unique.Set

import CSlash.Utils.Outputable
import CSlash.Types.SrcLoc
import CSlash.Data.Bag
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Constants (debugIsOn)
import CSlash.Types.Name.Reader

import Data.Coerce
import qualified Data.Semigroup as S
import Control.Monad ( msum, when )
import Data.Maybe ( mapMaybe, isJust )
import Data.List.NonEmpty ( NonEmpty )

-- these are for CheckTyEqResult
import Data.Word  ( Word8 )
import Data.List  ( intersperse )

{- *********************************************************************
*                                                                      *
*                       Canonical constraints                          *
*                                                                      *
********************************************************************* -}

type Cts = Bag Ct

data Ct
  = CNonCanonical CtEvidence

mkNonCanonical :: CtEvidence -> Ct
mkNonCanonical = CNonCanonical

ctEvidence :: Ct -> CtEvidence
ctEvidence (CNonCanonical ev) = ev

instance Outputable Ct where
  ppr ct = ppr (ctEvidence ct) <+> parens pp_short
    where
      pp_short = case ct of
                   CNonCanonical {} -> text "CNonCanonical"

{- *********************************************************************
*                                                                      *
                Wanted constraints
*                                                                      *
********************************************************************* -}

data WantedConstraints = WC
  { wc_simple :: Cts
  }

emptyWC :: WantedConstraints
emptyWC = WC { wc_simple = emptyBag }

isEmptyWC :: WantedConstraints -> Bool
isEmptyWC (WC { wc_simple = f }) = isEmptyBag f

addSimples :: WantedConstraints -> Cts -> WantedConstraints
addSimples wc cts = wc { wc_simple = wc_simple wc `unionBags` cts }

instance Outputable WantedConstraints where
  ppr (WC { wc_simple = s })
    = text "WC" <+> braces (vcat [ ppr_bag (text "wc_simple") s ])

ppr_bag :: Outputable a => SDoc -> Bag a -> SDoc
ppr_bag doc bag
  | isEmptyBag bag = empty
  | otherwise = hang (doc <+> equals) 2 (foldr (($$) . ppr) empty bag)

{- *********************************************************************
*                                                                      *
            CtEvidence
*                                                                      *
********************************************************************* -}

data CtEvidence
  = CtWantedKind
    { ctev_pred :: EvPred
    , ctev_loc :: CtLoc
    }

data EvPred
  = WantKindEq TcKind TcKind

ctEvPred :: CtEvidence -> EvPred
ctEvPred = ctev_pred

ctEvLoc :: CtEvidence -> CtLoc
ctEvLoc = ctev_loc

instance Outputable EvPred where
  ppr (WantKindEq k1 k2) = ppr k1 <+> ppr k2

instance Outputable CtEvidence where
  ppr ev = ppr (ctEvFlavor ev)
           <+> braces (ppr (ctl_depth (ctEvLoc ev)))
           <> dcolon <+> ppr (ctEvPred ev)

{- *********************************************************************
*                                                                      *
           CtFlavour
*                                                                      *
********************************************************************* -}

data CtFlavor
  = Given
  | Wanted
  deriving Eq

instance Outputable CtFlavor where
  ppr Given = text "[G]"
  ppr Wanted = text "[W]"

ctEvFlavor :: CtEvidence -> CtFlavor
ctEvFlavor (CtWantedKind {}) = Wanted

{- *********************************************************************
*                                                                      *
            SubGoalDepth
*                                                                      *
********************************************************************* -}

newtype SubGoalDepth = SubGoalDepth Int
  deriving (Eq, Ord, Outputable)

initialSubGoalDepth :: SubGoalDepth
initialSubGoalDepth = SubGoalDepth 0

{- *********************************************************************
*                                                                      *
            CtLoc
*                                                                      *
********************************************************************* -}

data CtLoc = CtLoc
  { ctl_origin :: CtOrigin
  , ctl_env :: CtLocEnv
  , ctl_depth :: !SubGoalDepth
  }
