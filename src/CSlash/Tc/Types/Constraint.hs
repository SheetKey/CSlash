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

ctLoc :: Ct -> CtLoc
ctLoc = ctEvLoc . ctEvidence

instance Outputable Ct where
  ppr ct = ppr (ctEvidence ct) <+> parens pp_short
    where
      pp_short = case ct of
                   CNonCanonical {} -> text "CNonCanonical"

isGivenLoc :: CtLoc -> Bool
isGivenLoc loc = isGivenOrigin (ctLocOrigin loc)

isWantedCt :: Ct -> Bool
isWantedCt = isWanted . ctEvidence

isGivenCt :: Ct -> Bool
isGivenCt = isGiven . ctEvidence

{- *********************************************************************
*                                                                      *
                Wanted constraints
*                                                                      *
********************************************************************* -}

data WantedConstraints = WC
  { wc_simple :: Cts
  , wc_impl :: Bag Implication
  }

emptyWC :: WantedConstraints
emptyWC = WC { wc_simple = emptyBag
             , wc_impl = emptyBag }

isEmptyWC :: WantedConstraints -> Bool
isEmptyWC (WC { wc_simple = f }) = isEmptyBag f

andWC :: WantedConstraints -> WantedConstraints -> WantedConstraints
andWC (WC { wc_simple = f1, wc_impl = i1 }) (WC { wc_simple = f2, wc_impl = i2 })
  = WC { wc_simple = f1 `unionBags` f2
       , wc_impl = i1 `unionBags` i2 }

addSimples :: WantedConstraints -> Cts -> WantedConstraints
addSimples wc cts = wc { wc_simple = wc_simple wc `unionBags` cts }

addImplics :: WantedConstraints -> Bag Implication -> WantedConstraints
addImplics wc implic = wc { wc_impl = wc_impl wc `unionBags` implic }

dropMisleading :: WantedConstraints -> WantedConstraints
dropMisleading (WC { wc_simple = simples, wc_impl = implics })
  = WC { wc_simple = filterBag insolubleWantedCt simples
       , wc_impl = mapBag drop_implic implics }
  where
    drop_implic implic = implic { ic_wanted = drop_wanted (ic_wanted implic) }
    drop_wanted (WC { wc_simple = simples, wc_impl = implics })
      = WC { wc_simple = filterBag keep_ct simples
           , wc_impl = mapBag drop_implic implics }

    keep_ct _ct = True

isInsolubleStatus :: ImplicStatus -> Bool
isInsolubleStatus IC_Insoluble = True
isInsolubleStatus IC_BadTelescope = True
isInsolubleStatus _ = False

insolubleImplic :: Implication -> Bool
insolubleImplic ic = isInsolubleStatus (ic_status ic)

insolubleWC :: WantedConstraints -> Bool
insolubleWC (WC { wc_impl = implics, wc_simple = simples })
  = anyBag insolubleWantedCt simples
    || anyBag insolubleImplic implics

insolubleWantedCt :: Ct -> Bool
insolubleWantedCt ct
  = insolubleCt ct
    && not (arisesFromGivens ct)

insolubleCt :: Ct -> Bool
insolubleCt (CNonCanonical {}) = False

instance Outputable WantedConstraints where
  ppr (WC { wc_simple = s })
    = text "WC" <+> braces (vcat [ ppr_bag (text "wc_simple") s ])

ppr_bag :: Outputable a => SDoc -> Bag a -> SDoc
ppr_bag doc bag
  | isEmptyBag bag = empty
  | otherwise = hang (doc <+> equals) 2 (foldr (($$) . ppr) empty bag)

{- *********************************************************************
*                                                                      *
            Implication constraints
*                                                                      *
********************************************************************* -}

data Implication = Implic
  { ic_tclvl :: TcLevel
  , ic_info :: SkolemInfoAnon
  , ic_skols :: [TcTyVar]
  , ic_given_eqs :: HasGivenEqs
  , ic_warn_inaccessible :: Bool
  , ic_env :: !CtLocEnv
  , ic_wanted :: WantedConstraints
  , ic_status :: ImplicStatus
  }

implicationPrototype :: CtLocEnv -> Implication
implicationPrototype ct_loc_env = Implic
  { ic_tclvl = panic "newImplic:tclvl"
  , ic_info = panic "newImplic:info"
  , ic_skols = []
  , ic_given_eqs = MaybeGivenEqs
  , ic_warn_inaccessible = panic "newImplic:warn_inaccessible"
  , ic_env = ct_loc_env
  , ic_wanted = emptyWC
  , ic_status = IC_Unsolved
  }

data ImplicStatus
  = IC_Solved
  | IC_Insoluble
  | IC_BadTelescope
  | IC_Unsolved

data HasGivenEqs
  = NoGivenEqs
  | LocalGivenEqs
  | MaybeGivenEqs
  deriving Eq

checkTelescopeSkol :: SkolemInfoAnon -> Bool
checkTelescopeSkol (ForAllSkol {}) = True
checkTelescopeSkol _ = False

{- *********************************************************************
*                                                                      *
            Invariant checking (debug only)
*                                                                      *
********************************************************************* -}

{-# INLINE checkImplicationInvariants #-}
checkImplicationInvariants :: (HasCallStack, Applicative m) => Implication -> m ()
checkImplicationInvariants implic = when debugIsOn (panic "check_implic implic")

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

arisesFromGivens :: Ct -> Bool
arisesFromGivens ct = isGivenCt ct || isGivenLoc (ctLoc ct)

instance Outputable EvPred where
  ppr (WantKindEq k1 k2) = ppr k1 <+> ppr k2

instance Outputable CtEvidence where
  ppr ev = ppr (ctEvFlavor ev)
           <+> braces (ppr (ctl_depth (ctEvLoc ev)))
           <> dcolon <+> ppr (ctEvPred ev)

isWanted :: CtEvidence -> Bool
isWanted (CtWantedKind {}) = True

isGiven :: CtEvidence -> Bool
isGiven (CtWantedKind {}) = False

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

ctLocOrigin :: CtLoc -> CtOrigin
ctLocOrigin = ctl_origin
