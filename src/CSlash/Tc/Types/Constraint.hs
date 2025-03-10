{-# LANGUAGE GeneralisedNewtypeDeriving #-}

module CSlash.Tc.Types.Constraint
  ( module CSlash.Tc.Types.Constraint
  , module CSlash.Tc.Types.CtLocEnv
  ) where

import Prelude hiding ((<>))

-- import GHC.Core.Predicate
import CSlash.Core.Type
import CSlash.Core.Kind
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
import Data.Bits
import Data.List  ( intersperse )

{- *********************************************************************
*                                                                      *
*                       Canonical constraints                          *
*                                                                      *
********************************************************************* -}

type KiXi = TcKind

type Cts = Bag Ct

data Ct
  = CNonCanonical CtEvidence

data EqCt = KiEqCt
  { eq_ev :: CtEvidence
  , eq_lhs :: CanEqLHS
  , eq_rhs :: KiXi
  }

data CanEqLHS
  = KiVarLHS TcKiVar

instance Outputable CanEqLHS where
  ppr (KiVarLHS kv) = ppr kv

data IrredCt = IrredCt
  { ir_ev :: CtEvidence
  , ir_reason :: CtIrredReason
  }

data CtIrredReason
  = NonCanonicalReason CheckTyKiEqResult

inInsolubleReason :: CtIrredReason -> Bool
inInsolubleReason (NonCanonicalReason ctker) = ctkerIsInsoluble ctker

newtype CheckTyKiEqResult = CTKER Word8

ctkeOK :: CheckTyKiEqResult
ctkeOK = CTKER zeroBits

ctkerHasNoProblem :: CheckTyKiEqResult -> Bool
ctkerHasNoProblem (CTKER 0) = True
ctkerHasNoProblem _ = False

newtype CheckTyKiEqProblem = CTKEP Word8

ctkeImpredicative = CTKEP (bit 0)
ctkeTypeFamily = CTKEP (bit 1)
ctkeInsolubleOccurs = CTKEP (bit 2)
ctkeSolubleOccurs = CTKEP (bit 3)
ctkeConcrete = CTKEP (bit 5)
ctkeSkolemEscape = CTKEP (bit 6)

ctkeProblem :: CheckTyKiEqProblem -> CheckTyKiEqResult
ctkeProblem (CTKEP mask) = CTKER mask

impredicativeProblem :: CheckTyKiEqResult
impredicativeProblem = ctkeProblem ctkeImpredicative

ctkerHasProblem :: CheckTyKiEqResult -> CheckTyKiEqProblem -> Bool
ctkerHasProblem (CTKER bits) (CTKEP mask) = (bits .&. mask) /= 0

ctkerIsInsoluble :: CheckTyKiEqResult -> Bool
ctkerIsInsoluble (CTKER bits) = (bits .&. mask) /= 0
  where
    mask = impredicative_mask .|. insoluble_occurs_mask
    CTKEP impredicative_mask = ctkeImpredicative
    CTKEP insoluble_occurs_mask = ctkeInsolubleOccurs

instance Semigroup CheckTyKiEqResult where
  CTKER bits1 <> CTKER bits2 = CTKER (bits1 .|. bits2)

instance Monoid CheckTyKiEqResult where
  mempty = ctkeOK

instance Eq CheckTyKiEqProblem where
  (CTKEP b1) == (CTKEP b2) = b1 == b2

instance Outputable CheckTyKiEqProblem where
  ppr prob@(CTKEP bits) = case lookup prob allBits of
                            Just s -> text s
                            Nothing -> text "unknown:" <+> ppr bits

instance Outputable CheckTyKiEqResult where
  ppr ctker
    | ctkerHasNoProblem ctker
    = text "ctkeOK"
    | otherwise
    = braces $ fcat $ intersperse vbar
      $ [ text str
        | (bitmask, str) <- allBits
        , ctker `ctkerHasProblem` bitmask ]

allBits :: [(CheckTyKiEqProblem, String)]
allBits = [ (ctkeImpredicative, "ctkeImpredicative")  
          , (ctkeTypeFamily, "ctkeTypeFamily")     
          , (ctkeInsolubleOccurs, "ctkeInsolubleOccurs")
          , (ctkeSolubleOccurs, "ctkeSolubleOccurs")  
          , (ctkeConcrete, "ctkeConcrete")   
          , (ctkeSkolemEscape, "ctkeSkolemEscape") ]


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

instance Outputable Implication where
  ppr (Implic { ic_tclvl = tclvl
              , ic_skols = skols
              , ic_given_eqs = given_eqs
              , ic_wanted = wanted
              , ic_status = status
              , ic_info = info })
    = hang (text "Implic" <+> lbrace)
      2 (sep [ text "TcLevel =" <+> ppr tclvl
             , text "Skolems =" <+> pprTyVars skols
             , text "Given-eqs =" <+> ppr given_eqs
             , text "Status =" <+> ppr status
             , hang (text "Wanted =") 2 (ppr wanted)
             , pprSkolInfo info ] <+> rbrace)

instance Outputable ImplicStatus where
  ppr IC_Insoluble = text "Insoluble"
  ppr IC_BadTelescope = text "Bad telescope"
  ppr IC_Unsolved = text "Unsolved"
  ppr IC_Solved = text "Solved"

checkTelescopeSkol :: SkolemInfoAnon -> Bool
checkTelescopeSkol (ForAllSkol {}) = True
checkTelescopeSkol _ = False

instance Outputable HasGivenEqs where
  ppr NoGivenEqs = text "NoGivenEqs"
  ppr LocalGivenEqs = text "LocalGivenEqs"
  ppr MaybeGivenEqs = text "MaybeGivenEqs"

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
  = CtWanted
    { ctev_pred :: Pred
    , ctev_loc :: CtLoc
    }

data Pred
  = KiEqPred TcKind TcKind

ctEvPred :: CtEvidence -> Pred
ctEvPred = ctev_pred

ctEvLoc :: CtEvidence -> CtLoc
ctEvLoc = ctev_loc

arisesFromGivens :: Ct -> Bool
arisesFromGivens ct = isGivenCt ct || isGivenLoc (ctLoc ct)

instance Outputable Pred where
  ppr (KiEqPred k1 k2) = ppr k1 <+> ppr k2

instance Outputable CtEvidence where
  ppr ev = ppr (ctEvFlavor ev)
           <+> braces (ppr (ctl_depth (ctEvLoc ev)))
           <> dcolon <+> ppr (ctEvPred ev)

isWanted :: CtEvidence -> Bool
isWanted (CtWanted {}) = True

isGiven :: CtEvidence -> Bool
isGiven (CtWanted {}) = False

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
ctEvFlavor (CtWanted {}) = Wanted

canKiEqLHS_maybe :: KiXi -> Maybe CanEqLHS
canKiEqLHS_maybe xi
  | Just kv <- getKiVar_maybe xi
  = Just $ KiVarLHS kv
  | otherwise
  = Nothing

canKiEqLHSKind :: CanEqLHS -> TcKind
canKiEqLHSKind (KiVarLHS kv) = mkKiVarKi kv

eqCanEqLHS :: CanEqLHS -> CanEqLHS -> Bool
eqCanEqLHS (KiVarLHS kv1) (KiVarLHS kv2) = kv1 == kv2

{- *********************************************************************
*                                                                      *
            SubGoalDepth
*                                                                      *
********************************************************************* -}

newtype SubGoalDepth = SubGoalDepth Int
  deriving (Eq, Ord, Outputable)

initialSubGoalDepth :: SubGoalDepth
initialSubGoalDepth = SubGoalDepth 0

bumpSubGoalDepth :: SubGoalDepth -> SubGoalDepth
bumpSubGoalDepth (SubGoalDepth n) = SubGoalDepth (n + 1)

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
 
bumpCtLocDepth :: CtLoc -> CtLoc
bumpCtLocDepth loc@(CtLoc { ctl_depth = d }) = loc { ctl_depth = bumpSubGoalDepth d }
