{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}

module CSlash.Tc.Types.Constraint
  ( module CSlash.Tc.Types.Constraint
  , module CSlash.Tc.Types.CtLocEnv
  ) where

import Prelude hiding ((<>))

import CSlash.Core.Predicate
import CSlash.Core.Type
import CSlash.Core.Type.Compare
import CSlash.Core.Type.FVs
import CSlash.Core.Kind
import CSlash.Core.Kind.FVs
-- import GHC.Core.Coercion
-- import GHC.Core.Class
import CSlash.Core.TyCon
import CSlash.Types.Name
import CSlash.Types.Var

import CSlash.Tc.Utils.TcType
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.CtLocEnv

import CSlash.Core

import CSlash.Core.Type.Ppr
import CSlash.Utils.FV
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

type TyCts = Bag TyCt
type KiCts = Bag KiCt

data KiCt
  = CIrredCanKi IrredKiCt
  | CKiCoCan KiCoCt
  | CNonCanonicalKi CtKiEvidence

data TyCt
  = CIrredCanTy IrredTyCt
  | CTyEqCan TyEqCt
  | CNonCanonicalTy CtTyEvidence

data KiCoCt = KiCoCt
  { kc_ev :: CtKiEvidence
  , kc_lhs :: CanKiCoLHS
  , kc_rhs :: AnyMonoKind
  , kc_pred :: KiPredCon
  }

data CanKiCoLHS
  = KiVarLHS AnyKiVar

data TyEqCt = TyEqCt
  { teq_ev :: CtTyEvidence
  , teq_lhs :: CanTyEqLHS
  , teq_rhs :: AnyType
  }

data CanTyEqLHS
  = TyVarLHS (AnyTyVar AnyKiVar)

instance Outputable CanKiCoLHS where
  ppr (KiVarLHS kv) = ppr kv

kiCoCtEvidence :: KiCoCt -> CtKiEvidence
kiCoCtEvidence = kc_ev

kiCoCtLHS :: KiCoCt -> CanKiCoLHS
kiCoCtLHS = kc_lhs

data IrredTyCt = IrredTyCt
  { itr_ev :: CtTyEvidence
  , itr_reason :: CtIrredReason
  }

data IrredKiCt = IrredKiCt
  { ikr_ev :: CtKiEvidence
  , ikr_reason :: CtIrredReason
  }

class IrredCt irred where
  insolubleIrredCt :: irred -> Bool

instance IrredCt IrredTyCt where
  insolubleIrredCt (IrredTyCt { itr_reason = reason })
    = isInsolubleReason reason

instance IrredCt IrredKiCt where
  insolubleIrredCt (IrredKiCt { ikr_reason = reason })
    = isInsolubleReason reason


irredCtEvidence :: IrredKiCt -> CtKiEvidence
irredCtEvidence = ikr_ev

irredCtPred :: IrredKiCt -> AnyPredKind
irredCtPred = ctKiEvPred . irredCtEvidence

instance Outputable IrredKiCt where
  ppr irred = ppr (CIrredCanKi irred)

instance Outputable IrredTyCt where
  ppr irred = ppr (CIrredCanTy irred)

data CtIrredReason
  = IrredShapeReason
  | NonCanonicalReason CheckTyKiEqResult
  | ShapeMismatchReason

instance Outputable CtIrredReason where
  ppr IrredShapeReason = text "(irred)"
  ppr (NonCanonicalReason ctker) = ppr ctker
  ppr ShapeMismatchReason = text "(shape)"

isInsolubleReason :: CtIrredReason -> Bool
isInsolubleReason IrredShapeReason = False
isInsolubleReason (NonCanonicalReason ctker) = ctkerIsInsoluble ctker
isInsolubleReason ShapeMismatchReason = True

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
ctkeCoercionHole = CTKEP (bit 4)
ctkeConcrete = CTKEP (bit 5)
ctkeSkolemEscape = CTKEP (bit 6)

ctkeProblem :: CheckTyKiEqProblem -> CheckTyKiEqResult
ctkeProblem (CTKEP mask) = CTKER mask

impredicativeProblem :: CheckTyKiEqResult
impredicativeProblem = ctkeProblem ctkeImpredicative

ctkerHasProblem :: CheckTyKiEqResult -> CheckTyKiEqProblem -> Bool
ctkerHasProblem (CTKER bits) (CTKEP mask) = (bits .&. mask) /= 0

ctkerHasOnlyProblems :: CheckTyKiEqResult -> CheckTyKiEqResult -> Bool
ctkerHasOnlyProblems (CTKER bits) (CTKER mask) = (bits .&. complement mask) == 0

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


mkNonCanonicalKi :: CtKiEvidence -> KiCt
mkNonCanonicalKi = CNonCanonicalKi

mkNonCanonicalTy :: CtTyEvidence -> TyCt
mkNonCanonicalTy = CNonCanonicalTy

mkKiGivens :: CtLoc -> [KiCoVar AnyKiVar] -> [KiCt]
mkKiGivens loc co_vars = map mk co_vars
  where mk co_var = mkNonCanonicalKi (CtKiGiven { ctkev_covar = co_var
                                                , ctkev_pred = kiCoVarPred co_var
                                                , ctkev_loc = loc })

mkTyGivens :: CtLoc -> [TyCoVar (AnyTyVar AnyKiVar) AnyKiVar] -> [TyCt]
mkTyGivens loc co_vars = map mk co_vars
  where
    mk co_var = mkNonCanonicalTy (CtTyGiven { cttev_covar = co_var
                                            , cttev_pred = tyCoVarPred co_var
                                            , cttev_loc = loc })

ctKiEvidence :: KiCt -> CtKiEvidence
ctKiEvidence (CKiCoCan (KiCoCt { kc_ev = ev })) = ev
ctKiEvidence (CIrredCanKi (IrredKiCt { ikr_ev = ev })) = ev
ctKiEvidence (CNonCanonicalKi ev) = ev

ctTyEvidence :: TyCt -> CtTyEvidence
ctTyEvidence (CIrredCanTy (IrredTyCt { itr_ev = ev })) = ev
ctTyEvidence (CTyEqCan (TyEqCt { teq_ev = ev })) = ev
ctTyEvidence (CNonCanonicalTy ev) = ev

updKiCtEvidence :: (CtKiEvidence -> CtKiEvidence) -> KiCt -> KiCt
updKiCtEvidence upd ct = case ct of
  CKiCoCan co@(KiCoCt { kc_ev = ev }) -> CKiCoCan (co { kc_ev = upd ev })
  CIrredCanKi ir@(IrredKiCt { ikr_ev = ev }) -> CIrredCanKi (ir { ikr_ev = upd ev })
  CNonCanonicalKi ev -> CNonCanonicalKi (upd ev)

ctKiPred :: KiCt -> AnyPredKind
ctKiPred ct = ctKiEvPred $ ctKiEvidence ct

ctKiCoVar :: KiCt -> KiCoVar AnyKiVar
ctKiCoVar ct = ctEvKiCoVar $ ctKiEvidence ct

instance Outputable KiCt where
  ppr ct = ppr (ctKiEvidence ct) <+> parens pp_sort
    where
      pp_sort = case ct of
                  CKiCoCan {} -> text "CKiCoCan"
                  CNonCanonicalKi {} -> text "CNonCanonicalKi"
                  CIrredCanKi (IrredKiCt { ikr_reason = reason })
                    -> text "CIrredCanKi" <> ppr reason

instance Outputable TyCt where
  ppr ct = ppr (ctTyEvidence ct) <+> parens pp_sort
    where
      pp_sort = case ct of
                  CTyEqCan {} -> text "CTyEqCan"
                  CNonCanonicalTy {} -> text "CNonCanonicalTy"
                  CIrredCanTy (IrredTyCt { itr_reason = reason })
                    -> text "CIrredCanTy" <> ppr reason

instance Outputable KiCoCt where
  ppr (KiCoCt { kc_ev = ev }) = ppr ev

instance Outputable TyEqCt where
  ppr (TyEqCt { teq_ev = ev }) = ppr ev

isGivenLoc :: CtLoc -> Bool
isGivenLoc loc = isGivenOrigin (ctLocOrigin loc)

{- *********************************************************************
*                                                                      *
                    CtEvidence
         The "flavor" of a canonical constraint
*                                                                      *
********************************************************************* -}

class Ct ct where
  ctLoc :: ct -> CtLoc
  ctOrigin :: ct -> CtOrigin
  isWantedCt :: ct -> Bool
  isGivenCt :: ct -> Bool
  insolubleCt :: ct -> Bool
  ctFlavor :: ct -> CtFlavor
  insolubleWantedCt :: ct -> Bool

instance Ct TyCt where
  ctLoc = ctEvLoc . ctTyEvidence
  ctOrigin = ctLocOrigin . ctLoc
  isWantedCt = isWanted . ctTyEvidence
  isGivenCt = isGiven . ctTyEvidence
  insolubleCt (CIrredCanTy itr_ct) = insolubleIrredCt itr_ct
  insolubleCt _ = False

  ctFlavor ct = ctEvFlavor $ ctTyEvidence ct

  insolubleWantedCt ct
    | CIrredCanTy itr_ct <- ct
    , IrredTyCt { itr_ev = ev } <- itr_ct
    , CtTyWanted { cttev_loc = loc, cttev_rewriters = rewriters } <- ev
    , insolubleIrredCt itr_ct
    , isEmptyTyRewriterSet rewriters
    , not (isGivenLoc loc)
    = True
    | otherwise
    = False

instance Ct KiCt where
  ctLoc = ctEvLoc . ctKiEvidence
  ctOrigin = ctLocOrigin . ctLoc
  isWantedCt = isWanted . ctKiEvidence
  isGivenCt = isGiven . ctKiEvidence
  insolubleCt (CIrredCanKi ikr_ct) = insolubleIrredCt ikr_ct
  insolubleCt _ = False

  ctFlavor (CKiCoCan kco_ct) = kiCoCtFlavor kco_ct
  ctFlavor ct = ctEvFlavor $ ctKiEvidence ct

  insolubleWantedCt ct
    | CIrredCanKi ikr_ct <- ct
    , IrredKiCt { ikr_ev = ev } <- ikr_ct
    , CtKiWanted { ctkev_loc = loc, ctkev_rewriters = rewriters } <- ev
    , insolubleIrredCt ikr_ct
    , isEmptyKiRewriterSet rewriters
    , not (isGivenLoc loc)
    = True
    | otherwise
    = False
  
extendCtsList :: Bag ct -> [ct] -> Bag ct
extendCtsList cts xs | null xs = cts
                     | otherwise = cts `unionBags` listToBag xs

andCts :: Bag ct -> Bag ct -> Bag ct
andCts = unionBags

consCts :: ct -> Bag ct -> Bag ct
consCts = consBag

emptyCts :: Bag ct
emptyCts = emptyBag

{- *********************************************************************
*                                                                      *
                Wanted constraints
*                                                                      *
********************************************************************* -}

data WantedKiConstraints = WKC
  { wkc_simple :: KiCts
  , wkc_impl :: Bag KiImplication
  }

data WantedTyConstraints = WTC
  { wtc_simple :: TyCts
  , wtc_impl :: Bag TyImplication
  , wtc_wkc :: WantedKiConstraints
  }

onlyWantedKiConstraints :: Monad m => WantedTyConstraints -> m WantedKiConstraints
onlyWantedKiConstraints wtc = case onlyWantedKiConstraints_maybe wtc of
  Just wkc -> return wkc
  _ -> pprPanic "onlyWantedKiConstraints" (ppr wtc)

onlyWantedKiConstraints_maybe :: WantedTyConstraints -> Maybe WantedKiConstraints
onlyWantedKiConstraints_maybe (WTC { wtc_simple = s, wtc_impl = i, wtc_wkc = wkc })
  | isEmptyBag s && isEmptyBag i
  = Just wkc
  | otherwise
  = Nothing

addTyInsols :: WantedTyConstraints -> Bag IrredTyCt -> WantedTyConstraints
addTyInsols wc insols = wc { wtc_simple = wtc_simple wc `unionBags` fmap CIrredCanTy insols }

class WC wc where
  emptyWC :: wc
  isEmptyWC :: wc -> Bool
  isSolvedWC :: wc -> Bool
  andWC :: wc -> wc -> wc
  dropMisleading :: wc -> wc
  insolubleWC :: wc -> Bool
  addKiSimples :: wc -> KiCts -> wc
  addKiImplics :: wc -> Bag KiImplication -> wc
  addKiInsols :: wc -> Bag IrredKiCt -> wc

instance WC WantedTyConstraints where
  emptyWC = WTC { wtc_simple = emptyBag
                , wtc_impl = emptyBag
                , wtc_wkc = emptyWC }
  isEmptyWC (WTC { wtc_simple = f
                 , wtc_impl = i
                 , wtc_wkc = wkc }) = isEmptyBag f && isEmptyBag i && isEmptyWC wkc
  isSolvedWC (WTC simple impl wkc) = isEmptyBag simple
                                     && allBag isSolvedImplic impl
                                     && isSolvedWC wkc
  andWC (WTC f1 i1 wkc1) (WTC f2 i2 wkc2)
    = WTC { wtc_simple = f1 `unionBags` f2
          , wtc_impl = i1 `unionBags` i2
          , wtc_wkc = wkc1 `andWC` wkc2 }

  dropMisleading (WTC { wtc_simple = simples, wtc_impl = implics, wtc_wkc = wkc })
    = WTC { wtc_simple = filterBag insolubleWantedCt simples
         , wtc_impl = mapBag drop_implic implics
         , wtc_wkc = dropMisleading wkc }
    where
      drop_implic implic = implic { tic_wanted = drop_wanted (tic_wanted implic) }
      drop_wanted (WTC { wtc_simple = simples, wtc_impl = implics, wtc_wkc = wkc })
        = WTC { wtc_simple = simples
              , wtc_impl = mapBag drop_implic implics
              , wtc_wkc = dropMisleading wkc } -- might be wrong??
  
  insolubleWC (WTC { wtc_impl = implics, wtc_simple = simples, wtc_wkc = wkc })
    = anyBag insolubleWantedCt simples
      || anyBag insolubleImplic implics
      || insolubleWC wkc

  addKiSimples wc@(WTC { wtc_wkc = wkc }) cts
    = wc { wtc_wkc = wkc { wkc_simple = wkc_simple wkc `unionBags` cts } }

  addKiImplics wc@(WTC {wtc_wkc = wkc }) implic
    = wc { wtc_wkc = wkc { wkc_impl = wkc_impl wkc `unionBags` implic } }

  addKiInsols wc@(WTC { wtc_wkc = wkc }) insols
    = wc { wtc_wkc = wkc { wkc_simple = wkc_simple wkc `unionBags` fmap CIrredCanKi insols } }

instance WC WantedKiConstraints where
  emptyWC = WKC { wkc_simple = emptyBag
                , wkc_impl = emptyBag }
  isEmptyWC (WKC { wkc_simple = f
                 , wkc_impl = i }) = isEmptyBag f && isEmptyBag i 
  isSolvedWC (WKC simple impl) = isEmptyBag simple
                                 && allBag isSolvedImplic impl
  andWC (WKC f1 i1) (WKC f2 i2)
    = WKC { wkc_simple = f1 `unionBags` f2
          , wkc_impl = i1 `unionBags` i2 }

  dropMisleading (WKC { wkc_simple = simples, wkc_impl = implics })
    = WKC { wkc_simple = filterBag insolubleWantedCt simples
          , wkc_impl = mapBag drop_implic implics }
    where
      drop_implic implic = implic { kic_wanted = drop_wanted (kic_wanted implic) }
      drop_wanted (WKC { wkc_simple = simples, wkc_impl = implics })
        = WKC { wkc_simple = simples
             , wkc_impl = mapBag drop_implic implics }

  insolubleWC (WKC { wkc_impl = implics, wkc_simple = simples })
    = anyBag insolubleWantedCt simples
      || anyBag insolubleImplic implics

  addKiSimples wc cts = wc { wkc_simple = wkc_simple wc `unionBags` cts }

  addKiImplics wc implic = wc { wkc_impl = wkc_impl wc `unionBags` implic }

  addKiInsols wc insols = wc { wkc_simple = wkc_simple wc `unionBags` fmap CIrredCanKi insols }

mkTyImplicWC :: Bag TyImplication -> WantedTyConstraints
mkTyImplicWC implic = emptyWC { wtc_impl = implic }

mkKiImplicWC :: Bag KiImplication -> WantedKiConstraints
mkKiImplicWC implic = emptyWC { wkc_impl = implic }

addTySimples :: WantedTyConstraints -> TyCts -> WantedTyConstraints
addTySimples wc cts = wc { wtc_simple = wtc_simple wc `unionBags` cts }

addTyImplics :: WantedTyConstraints -> Bag TyImplication -> WantedTyConstraints
addTyImplics wc implic = wc { wtc_impl = wtc_impl wc `unionBags` implic }

isSolvedStatus :: ImplicStatus dead -> Bool
isSolvedStatus IC_Solved {} = True
isSolvedStatus _ = False

isInsolubleStatus :: ImplicStatus dead -> Bool
isInsolubleStatus IC_Insoluble = True
isInsolubleStatus IC_BadTelescope = True
isInsolubleStatus _ = False

instance Outputable WantedTyConstraints where
  ppr (WTC { wtc_simple = s, wtc_impl = i, wtc_wkc = wkc })
    = text "WTC" <+> braces (vcat [ ppr_bag (text "wtc_simple") s
                                  , ppr_bag (text "wtc_impl") i
                                  , text "wtc_wkc =" <+> ppr wkc ])

instance Outputable WantedKiConstraints where
  ppr (WKC { wkc_simple = s, wkc_impl = i })
    = text "WKC" <+> braces (vcat [ ppr_bag (text "wkc_simple") s
                                  , ppr_bag (text "wkc_impl") i ])

ppr_bag :: Outputable a => SDoc -> Bag a -> SDoc
ppr_bag doc bag
  | isEmptyBag bag = empty
  | otherwise = hang (doc <+> equals) 2 (foldr (($$) . ppr) empty bag)

{- *********************************************************************
*                                                                      *
            Implication constraints
*                                                                      *
********************************************************************* -}

data TyImplication
  = TyImplic
    { tic_tclvl :: TcLevel
    , tic_info :: SkolemInfoAnon
    , tic_skols :: [TcTyVar AnyKiVar]
    , tic_given :: [TyCoVar (AnyTyVar AnyKiVar) AnyKiVar]
    , tic_given_eqs :: HasGivenTyEqs
    , tic_warn_inaccessible :: Bool
    , tic_env :: !CtLocEnv
    , tic_wanted :: WantedTyConstraints
    , tic_binds :: TyCoBindsVar
    , tic_status :: ImplicStatus (TyCoVar (AnyTyVar AnyKiVar) AnyKiVar)
    , tic_need_inner :: MkVarSet (TyCoVar (AnyTyVar AnyKiVar) AnyKiVar)
    , tic_need_outer :: MkVarSet (TyCoVar (AnyTyVar AnyKiVar) AnyKiVar)
    }

data KiImplication
  = KiImplic
    { kic_tclvl :: TcLevel
    , kic_info :: SkolemInfoAnon
    , kic_skols :: [TcKiVar] -- as in GHC (NO KiVars or MetaKiVars, just Skolem TcKiVars)
    , kic_given :: [KiCoVar AnyKiVar]
    , kic_given_kicos :: HasGivenKiCos
    , kic_warn_inaccessible :: Bool
    , kic_env :: !CtLocEnv
    , kic_wanted :: WantedKiConstraints
    , kic_binds :: KiCoBindsVar
    , kic_status :: ImplicStatus (KiCoVar AnyKiVar)
    , kic_need_inner :: MkVarSet (KiCoVar AnyKiVar)
    , kic_need_outer :: MkVarSet (KiCoVar AnyKiVar)
    }

class Implic impl where
  implicationPrototype :: CtLocEnv -> impl
  isSolvedImplic :: impl -> Bool
  getUserGivensFromImplics :: [impl] -> [impl]
  insolubleImplic :: impl -> Bool
  setWarnInaccessible :: Bool -> impl -> impl

instance Implic TyImplication where
  implicationPrototype ct_loc_env = TyImplic
    { tic_tclvl = panic "newTyImplic:tclvl"
    , tic_binds = panic "newTyImplic:binds"
    , tic_info = panic "newTyImplic:info"
    , tic_skols = []
    , tic_given = []
    , tic_given_eqs = MaybeGivenTyEqs
    , tic_warn_inaccessible = panic "newTyImplic:warn_inaccessible"
    , tic_env = ct_loc_env
    , tic_wanted = emptyWC
    , tic_status = IC_Unsolved
    , tic_need_inner = emptyVarSet
    , tic_need_outer = emptyVarSet
    }

  isSolvedImplic (TyImplic { tic_status = status }) = isSolvedStatus status
  insolubleImplic ic = isInsolubleStatus (tic_status ic)

  getUserGivensFromImplics implics = reverse (filterOut (null . tic_given) implics)

  setWarnInaccessible f ti = ti { tic_warn_inaccessible = f }

instance Implic KiImplication where
  implicationPrototype ct_loc_env = KiImplic
    { kic_tclvl = panic "newImplic:tclvl"
    , kic_binds = panic "newImplic:binds"
    , kic_info = panic "newImplic:info"
    , kic_skols = []
    , kic_given = []
    , kic_given_kicos = MaybeGivenKiCos
    , kic_warn_inaccessible = panic "newImplic:warn_inaccessible"
    , kic_env = ct_loc_env
    , kic_wanted = emptyWC
    , kic_status = IC_Unsolved
    , kic_need_inner = emptyVarSet
    , kic_need_outer = emptyVarSet
    }

  isSolvedImplic (KiImplic { kic_status = status }) = isSolvedStatus status
  insolubleImplic ic = isInsolubleStatus (kic_status ic)

  getUserGivensFromImplics implics = reverse (filterOut (null . kic_given) implics)

  setWarnInaccessible f ki = ki { kic_warn_inaccessible = f }

data ImplicStatus dead
  = IC_Solved { ics_dead :: [dead] }
  | IC_Insoluble
  | IC_BadTelescope
  | IC_Unsolved

data HasGivenKiCos
  = NoGivenKiCos
  | LocalGivenKiCos
  | MaybeGivenKiCos
  deriving Eq

data HasGivenTyEqs
  = NoGivenTyEqs
  | LocalGivenTyEqs
  | MaybeGivenTyEqs
  deriving Eq

instance Outputable TyImplication where
  ppr (TyImplic { tic_tclvl = tclvl
                , tic_skols = skols
                , tic_given = given
                , tic_given_eqs = given_eqs
                , tic_wanted = wanted
                , tic_status = status
                , tic_info = info })
    = hang (text "TyImplic" <+> lbrace)
      2 (sep [ text "TcLevel =" <+> ppr tclvl
             , text "Skolems =" <+> ppr skols
             , text "Given-eqs =" <+> ppr given_eqs
             , text "Status =" <+> ppr status
             , hang (text "Given =") 2 (pprTyCoVars given)
             , hang (text "Wanted =") 2 (ppr wanted)
             , pprSkolInfo info ] <+> rbrace)

instance Outputable KiImplication where
  ppr (KiImplic { kic_tclvl = tclvl
                , kic_skols = skols
                , kic_given = given
                , kic_given_kicos = given_kicos
                , kic_wanted = wanted
                , kic_status = status
                , kic_info = info })
    = hang (text "KiImplic" <+> lbrace)
      2 (sep [ text "TcLevel =" <+> ppr tclvl
             , text "Skolems =" <+> ppr skols
             , text "Given-kicos =" <+> ppr given_kicos
             , text "Status =" <+> ppr status
             , hang (text "Given =") 2 (pprKiCoVars given)
             , hang (text "Wanted =") 2 (ppr wanted)
             , pprSkolInfo info ] <+> rbrace)

instance Outputable dead =>  Outputable (ImplicStatus dead) where
  ppr IC_Insoluble = text "Insoluble"
  ppr IC_BadTelescope = text "Bad telescope"
  ppr IC_Unsolved = text "Unsolved"
  ppr (IC_Solved dead) = text "Solved" <+> (braces (text "Dead givens =" <+> ppr dead))

-- Probably don't need to do this.
-- This was part of GHC's strategy to avoid skolem escape, a problem which we do not have.
checkTelescopeSkol :: SkolemInfoAnon -> Bool
checkTelescopeSkol (ForAllSkol {}) = True
checkTelescopeSkol _ = False

instance Outputable HasGivenKiCos where
  ppr NoGivenKiCos = text "NoGivenKiCos"
  ppr LocalGivenKiCos = text "LocalGivenKiCos"
  ppr MaybeGivenKiCos = text "MaybeGivenKiCos"

instance Outputable HasGivenTyEqs where
  ppr NoGivenTyEqs = text "NoGivenTyEqs"
  ppr LocalGivenTyEqs = text "LocalGivenTyEqs"
  ppr MaybeGivenTyEqs = text "MaybeGivenTyEqs"

{- *********************************************************************
*                                                                      *
            Invariant checking (debug only)
*                                                                      *
********************************************************************* -}

{-# INLINE checkTyImplicationInvariants #-}
checkTyImplicationInvariants :: (HasCallStack, Applicative m) => TyImplication -> m ()
checkTyImplicationInvariants implic = when debugIsOn (check_ty_implic implic)

check_ty_implic :: (HasCallStack, Applicative m) => TyImplication -> m ()
check_ty_implic implic@(TyImplic { tic_tclvl = lvl, tic_info = skol_info, tic_skols = skols })
  | null bads = pure ()
  | otherwise = massertPpr False $ vcat [ text "checkTyImplicationInvariants failure"
                                        , nest 2 $ vcat bads
                                        , ppr implic ]
  where
    bads = mapMaybe check skols

    check :: TcTyVar AnyKiVar -> Maybe SDoc
    check tv = check_details tv (tcVarDetails tv)

    check_details :: TcTyVar AnyKiVar -> TcVarDetails AnyType -> Maybe SDoc
    check_details tv (SkolemVar tv_skol_info tv_lvl)
      | not (tv_lvl `sameDepthAs` lvl)
      = Just $ vcat [ ppr tv <+> text "has level" <+> ppr tv_lvl
                    , text "tic_lvl" <+> ppr lvl ]
      | not (skol_info `checkSkolInfoAnon` skol_info_anon)
      = Just $ vcat [ ppr tv <+> text "has skol info" <+> ppr skol_info_anon
                    , text "tic_info" <+> ppr skol_info ]
      | otherwise
      = Nothing
      where
        skol_info_anon = getSkolemInfo tv_skol_info
    check_details tv details = Just (ppr tv <+> text "is not a SkolemTv" <+> ppr details)

{-# INLINE checkKiImplicationInvariants #-}
checkKiImplicationInvariants :: (HasCallStack, Applicative m) => KiImplication -> m ()
checkKiImplicationInvariants implic = when debugIsOn (check_ki_implic implic)

check_ki_implic :: (HasCallStack, Applicative m) => KiImplication -> m ()
check_ki_implic implic@(KiImplic { kic_tclvl = lvl, kic_info = skol_info, kic_skols = skols })
  | null bads = pure ()
  | otherwise = massertPpr False (vcat [ text "checkImplicationInvariants failure"
                                       , nest 2 (vcat bads)
                                       , ppr implic ])
  where
    bads = mapMaybe check skols

    check :: TcKiVar -> Maybe SDoc
    check kv = check_details kv (tcVarDetails kv)

    check_details :: TcKiVar -> TcVarDetails AnyMonoKind -> Maybe SDoc
    check_details kv (SkolemVar kv_skol_info tv_lvl)
      | not (tv_lvl `sameDepthAs` lvl)
      = Just (vcat [ ppr kv <+> text "has level" <+> ppr tv_lvl
                   , text "ic_lvl" <+> ppr lvl ])
      | not (skol_info `checkSkolInfoAnon` skol_info_anon)
      = Just (vcat [ ppr kv <+> text "has skol info" <+> ppr skol_info_anon
                   , text "ic_info" <+> ppr skol_info ])
      | otherwise
      = Nothing
      where
        skol_info_anon = getSkolemInfo kv_skol_info
    check_details kv details = Just (ppr kv <+> text "is not a SkolemVar" <+> ppr details)

checkSkolInfoAnon :: SkolemInfoAnon -> SkolemInfoAnon -> Bool
checkSkolInfoAnon sk1 sk2 = go sk1 sk2
  where
    go (SigSkol c1 t1 s1) (SigSkol c2 t2 s2) = c1 == c2 && t1 `tcEqType` t2 && s1 == s2
    go (SigTypeSkol cx1) (SigTypeSkol cx2) = cx1 == cx2
    go (ForAllSkol _) (ForAllSkol _) = True
    go (TyLamTySkol ids1) (TyLamTySkol ids2)
      = equalLength ids1 ids2 && and (zipWith (==) ids1 ids2)
    go (InferSkol ids1) (InferSkol ids2)
      = equalLength ids1 ids2 && and (zipWith eq_pr ids1 ids2)
    go (UnifyForAllSkol t1) (UnifyForAllSkol t2) = t1 `tcEqType` t2
    go (TyConSkol f1 n1) (TyConSkol f2 n2) = f1 == f2 && n1 == n2
    go (UnkSkol _) (UnkSkol _) = True
    go (ForAllSkol _) _ = True
    go _ _ = False

    eq_pr (i1, _) (i2, _) = i1 == i2

{- *********************************************************************
*                                                                      *
        Simple functions over evidence variables
*                                                                      *
********************************************************************* -}

type AnyTyFV = TyFV (KiCoVar AnyKiVar) AnyKiVar
type AnyKiFV = KiFV AnyKiVar

varsOfKiCt :: KiCt -> AnyKiVarSet
varsOfKiCt ct = case fvVarAcc (fvsOfKiCt ct) of
  (_, kvs) -> kvs

fvsOfKiCt :: KiCt -> AnyKiFV
fvsOfKiCt ct = fvsOfMonoKind $ ctKiPred ct

varsOfKiCts :: KiCts -> AnyKiVarSet
varsOfKiCts cts = case fvVarAcc (fvsOfKiCts cts) of
  (_, kvs) -> kvs

fvsOfKiCts :: KiCts -> AnyKiFV
fvsOfKiCts = foldr (unionFV . fvsOfKiCt) emptyFV

varsOfWKC :: WantedKiConstraints -> (MkVarSet (KiCoVar AnyKiVar), MkVarSet AnyKiVar)
varsOfWKC wc = case fvVarAcc (fvsOfWKC wc) of
  (_, tvs, _, kvs) -> (tvs, kvs)

varsOfWKCList :: WantedKiConstraints -> ([KiCoVar AnyKiVar], [AnyKiVar])
varsOfWKCList wc = case fvVarAcc (fvsOfWKC wc) of
  (tvs, _, kvs, _) -> (tvs, kvs)

fvsOfWKC :: WantedKiConstraints -> AnyTyFV
fvsOfWKC (WKC { wkc_simple = simple, wkc_impl = implic })
  = liftKiFV (fvsOfKiCts simple) `unionFV` fvsOfBag fvsOfKiImplic implic

fvsOfKiImplic :: KiImplication -> AnyTyFV
fvsOfKiImplic (KiImplic { kic_skols = skols, kic_given = givens, kic_wanted = wanted })
  | isEmptyWC wanted
  = emptyFV
  | otherwise
  = fvsKiVarBndrs (toAnyKiVar <$> skols)
    $ fvsVarBndrs givens
    $ fvsOfWKC wanted

fvsOfBag :: (a -> AnyTyFV) -> Bag a -> AnyTyFV
fvsOfBag vs_of = foldr (unionFV . vs_of) emptyFV

{- *********************************************************************
*                                                                      *
            Pretty printing
*                                                                      *
********************************************************************* -}

pprTyCoVars :: [TyCoVar (AnyTyVar AnyKiVar) AnyKiVar] -> SDoc
pprTyCoVars co_vars = vcat (map pprTyCoVarWithType co_vars)

pprKiCoVars :: [KiCoVar AnyKiVar] -> SDoc
pprKiCoVars co_vars = vcat (map pprKiCoVarWithKind co_vars)

pprKiCoVarTheta :: [KiCoVar AnyKiVar] -> SDoc
pprKiCoVarTheta co_vars = pprTheta (map kiCoVarPred co_vars)
  where
    pprTheta t = text "pprTheta NEEDS IMPLEMENTING" <+> ppr t

pprKiCoVarWithKind :: KiCoVar AnyKiVar -> SDoc
pprKiCoVarWithKind v = ppr v <+> colon <+> ppr (kiCoVarPred v)

pprTyCoVarWithType :: TyCoVar (AnyTyVar AnyKiVar) AnyKiVar -> SDoc
pprTyCoVarWithType v = ppr v <+> colon <+> ppr (tyCoVarPred v)

{- *********************************************************************
*                                                                      *
            CtEvidence
*                                                                      *
********************************************************************* -}

data CtTyEvidence
  = CtTyGiven
    { cttev_pred :: AnyPredType
    , cttev_covar :: TyCoVar (AnyTyVar AnyKiVar) AnyKiVar
    , cttev_loc :: CtLoc
    }
  | CtTyWanted
    { cttev_pred :: AnyPredType
    , cttev_dest :: AnyTypeCoercionHole
    , cttev_loc :: CtLoc
    , cttev_rewriters :: TyRewriterSet
    }

data CtKiEvidence
  = CtKiGiven
    { ctkev_pred :: AnyPredKind
    , ctkev_covar :: KiCoVar AnyKiVar
    , ctkev_loc :: CtLoc }
  | CtKiWanted
    { ctkev_pred :: AnyPredKind
    , ctkev_dest :: KindCoercionHole AnyKiVar
    , ctkev_loc :: CtLoc
    , ctkev_rewriters :: KiRewriterSet
    }

class CtEv ev where
  ctEvLoc :: ev -> CtLoc

  isWanted :: ev -> Bool
  isGiven :: ev -> Bool

  ctEvFlavor :: ev -> CtFlavor

instance CtEv CtTyEvidence where
  ctEvLoc = cttev_loc

  isWanted (CtTyWanted {}) = True
  isWanted _ = False

  isGiven (CtTyGiven {}) = True
  isGiven _ = False

  ctEvFlavor (CtTyWanted {}) = Wanted
  ctEvFlavor (CtTyGiven {}) = Given

instance CtEv CtKiEvidence where
  ctEvLoc = ctkev_loc

  isWanted (CtKiWanted {}) = True
  isWanted _ = False

  isGiven (CtKiGiven {}) = True
  isGiven _ = False

  ctEvFlavor (CtKiWanted {}) = Wanted
  ctEvFlavor (CtKiGiven {}) = Given

ctKiEvPred :: CtKiEvidence -> AnyPredKind
ctKiEvPred = ctkev_pred

ctTyEvPred :: CtTyEvidence -> AnyPredType
ctTyEvPred = cttev_pred

ctKiEvRewriters :: CtKiEvidence -> KiRewriterSet
ctKiEvRewriters (CtKiWanted { ctkev_rewriters = rewriters }) = rewriters
ctKiEvRewriters _ = emptyKiRewriterSet

ctTyEvRewriters :: CtTyEvidence -> TyRewriterSet
ctTyEvRewriters (CtTyWanted { cttev_rewriters = rewriters }) = rewriters
ctTyEvRewriters _ = emptyTyRewriterSet

ctEvKiCoercion :: HasDebugCallStack => CtKiEvidence -> KindCoercion AnyKiVar
ctEvKiCoercion (CtKiGiven { ctkev_pred = pred, ctkev_covar = co_var })
  = mkKiCoVarCo co_var
ctEvKiCoercion (CtKiWanted { ctkev_dest = hole })
  = mkKiHoleCo hole

ctEvTyCoercion :: HasDebugCallStack => CtTyEvidence -> AnyTypeCoercion
ctEvTyCoercion (CtTyGiven { cttev_pred = pred, cttev_covar = co_var })
  = mkTyCoVarCo co_var
ctEvTyCoercion (CtTyWanted { cttev_dest = hole })
  = mkTyHoleCo hole

ctEvKiCoVar :: CtKiEvidence -> KiCoVar AnyKiVar
ctEvKiCoVar (CtKiWanted { ctkev_dest = h }) = coHoleCoVar h
ctEvKiCoVar (CtKiGiven { ctkev_covar = ev }) = ev

setCtEvPredKind :: CtKiEvidence -> AnyPredKind -> CtKiEvidence
setCtEvPredKind old_ctev@(CtKiGiven { ctkev_covar = co }) new_pred
  = old_ctev { ctkev_pred = new_pred
             , ctkev_covar = setVarKind co new_pred }
setCtEvPredKind old_ctev@(CtKiWanted { ctkev_dest = hole }) new_pred
  = old_ctev { ctkev_pred = new_pred, ctkev_dest = new_hole }
  where
    new_hole = (setCoHoleKind hole new_pred)

instance Outputable CtKiEvidence where
  ppr ev = ppr (ctEvFlavor ev)
           <+> braces (ppr (ctl_depth (ctEvLoc ev)))
           <> dcolon <+> ppr (ctKiEvPred ev)

instance Outputable CtTyEvidence where
  ppr ev = ppr (ctEvFlavor ev)
           <+> braces (ppr (ctl_depth (ctEvLoc ev)))
           <> dcolon <+> ppr (ctTyEvPred ev)

{- *********************************************************************
*                                                                      *
           RewriterSet
*                                                                      *
********************************************************************* -}

type RWKiCoHole = KindCoercionHole AnyKiVar

newtype KiRewriterSet = KiRewriterSet (UniqSet RWKiCoHole)
  deriving newtype (Outputable, Semigroup, Monoid)

type RWTyCoHole = AnyTypeCoercionHole

newtype TyRewriterSet = TyRewriterSet (UniqSet RWTyCoHole)
  deriving newtype (Outputable, Semigroup, Monoid)

emptyKiRewriterSet :: KiRewriterSet
emptyKiRewriterSet = KiRewriterSet emptyUniqSet

emptyTyRewriterSet :: TyRewriterSet
emptyTyRewriterSet = TyRewriterSet emptyUniqSet

unitKiRewriterSet :: RWKiCoHole -> KiRewriterSet
unitKiRewriterSet = coerce (unitUniqSet @RWKiCoHole)

unionKiRewriterSet :: KiRewriterSet -> KiRewriterSet -> KiRewriterSet
unionKiRewriterSet = coerce (unionUniqSets @RWKiCoHole)

isEmptyKiRewriterSet :: KiRewriterSet -> Bool
isEmptyKiRewriterSet = coerce (isEmptyUniqSet @RWKiCoHole)

isEmptyTyRewriterSet :: TyRewriterSet -> Bool
isEmptyTyRewriterSet = coerce (isEmptyUniqSet @RWTyCoHole)

addKiRewriter :: KiRewriterSet -> RWKiCoHole -> KiRewriterSet
addKiRewriter = coerce (addOneToUniqSet @RWKiCoHole)

kiRewriterSetFromCts :: Bag KiCt -> KiRewriterSet
kiRewriterSetFromCts cts = foldr add emptyKiRewriterSet cts
  where
    add ct rw_set = case ctKiEvidence ct of
                      CtKiWanted { ctkev_dest = hole } -> rw_set `addKiRewriter` hole
                      _ -> rw_set

{- *********************************************************************
*                                                                      *
           CtFlavor
*                                                                      *
********************************************************************* -}

data CtFlavor
  = Given
  | Wanted
  deriving Eq

instance Outputable CtFlavor where
  ppr Given = text "[G]"
  ppr Wanted = text "[W]"

kiCoCtFlavor :: KiCoCt -> CtFlavor
kiCoCtFlavor (KiCoCt { kc_ev = ev }) = ctEvFlavor ev

canKiCoLHS_maybe :: AnyMonoKind -> Maybe CanKiCoLHS
canKiCoLHS_maybe xi
  | Just kv <- getKiVar_maybe xi
  = Just $ KiVarLHS kv
  | otherwise
  = Nothing

canKiCoLHSKind :: CanKiCoLHS -> AnyMonoKind
canKiCoLHSKind (KiVarLHS kv) = mkKiVarKi kv

eqCanKiCoLHS :: CanKiCoLHS -> CanKiCoLHS -> Bool
eqCanKiCoLHS (KiVarLHS kv1) (KiVarLHS kv2) = kv1 == kv2

eqCanRewriteF :: CtFlavor -> CtFlavor -> Bool
eqCanRewriteF Given _ = True
eqCanRewriteF Wanted Wanted = True
eqCanRewriteF Wanted Given = False

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

subGoalDepthExceeded :: IntWithInf -> SubGoalDepth -> Bool
subGoalDepthExceeded reductionDepth (SubGoalDepth d) = mkIntWithInf d > reductionDepth

{- *********************************************************************
*                                                                      *
            CtLoc
*                                                                      *
********************************************************************* -}

data CtLoc = CtLoc
  { ctl_origin :: CtOrigin
  , ctl_env :: CtLocEnv
  , ctl_t_or_k :: Maybe TypeOrKind
  , ctl_depth :: !SubGoalDepth
  }

mkKindEqLoc :: AnyType -> AnyType -> CtLoc -> CtLoc
mkKindEqLoc t1 t2 ctloc
  | CtLoc { ctl_t_or_k = t_or_k, ctl_origin = origin } <- ctloc
  = assert (t_or_k /= Just KindLevel) 
    $ ctloc { ctl_origin = KindEqOrigin t1 t2 origin
            , ctl_t_or_k = Just KindLevel }

adjustCtLoc :: Bool -> Bool -> CtLoc -> CtLoc
adjustCtLoc is_vis is_kind loc = loc2
  where
    loc1 | is_kind = toKindLoc loc
         | otherwise = loc
    loc2 | is_vis = loc1
         | otherwise = toInvisibleLoc loc1

adjustCtLocKind :: CtLoc -> CtLoc
adjustCtLocKind = toInvisibleLoc . toKindLoc

toKindLoc :: CtLoc -> CtLoc
toKindLoc loc = loc { ctl_t_or_k = Just KindLevel }

toInvisibleLoc :: CtLoc -> CtLoc
toInvisibleLoc loc = updateCtLocOrigin loc toInvisibleOrigin

mkGivenLoc :: TcLevel -> SkolemInfoAnon -> CtLocEnv -> CtLoc
mkGivenLoc tclvl skol_info env
  = CtLoc { ctl_origin = GivenOrigin skol_info
          , ctl_env = setCtLocEnvLvl env tclvl
          , ctl_t_or_k = Nothing
          , ctl_depth = initialSubGoalDepth }

ctLocEnv :: CtLoc -> CtLocEnv
ctLocEnv = ctl_env

ctLocLevel :: CtLoc -> TcLevel
ctLocLevel loc = getCtLocEnvLvl (ctLocEnv loc)

ctLocDepth :: CtLoc -> SubGoalDepth
ctLocDepth = ctl_depth

ctLocOrigin :: CtLoc -> CtOrigin
ctLocOrigin = ctl_origin

ctLocSpan :: CtLoc -> RealSrcSpan
ctLocSpan (CtLoc { ctl_env = lcl }) = getCtLocEnvLoc lcl

ctLocTypeOrKind_maybe :: CtLoc -> Maybe TypeOrKind
ctLocTypeOrKind_maybe = ctl_t_or_k
 
bumpCtLocDepth :: CtLoc -> CtLoc
bumpCtLocDepth loc@(CtLoc { ctl_depth = d }) = loc { ctl_depth = bumpSubGoalDepth d }

setCtLocOrigin :: CtLoc -> CtOrigin -> CtLoc
setCtLocOrigin ctl orig = ctl { ctl_origin = orig }

updateCtLocOrigin :: CtLoc -> (CtOrigin -> CtOrigin) -> CtLoc
updateCtLocOrigin ctl@(CtLoc { ctl_origin = orig }) upd
  = ctl { ctl_origin = upd orig }

pprCtLoc :: CtLoc -> SDoc
pprCtLoc (CtLoc { ctl_origin = o, ctl_env = lcl })
  = sep [ pprCtOrigin o, text "at" <+> ppr (getCtLocEnvLoc lcl) ]
