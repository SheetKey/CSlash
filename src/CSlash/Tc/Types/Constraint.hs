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

type Cts = Bag Ct

data Ct
  = CIrredCan IrredCt
  | CEqCan EqCt
  | CRelCan RelCt
  | CNonCanonical CtEvidence

data RelCt = RelCt
  { rl_ev :: CtEvidence
  , rl_kc :: KiCon
  , rl_ki1 :: AnyMonoKind
  , rl_ki2 :: AnyMonoKind
  }
  
relCtEvidence :: RelCt -> CtEvidence
relCtEvidence = rl_ev

instance Outputable RelCt where
  ppr rel = ppr (CRelCan rel)

data EqCt = KiEqCt
  { eq_ev :: CtEvidence
  , eq_lhs :: CanEqLHS
  , eq_rhs :: AnyMonoKind
  }

data CanEqLHS
  = KiVarLHS AnyKiVar

instance Outputable CanEqLHS where
  ppr (KiVarLHS kv) = ppr kv

eqCtEvidence :: EqCt -> CtEvidence
eqCtEvidence = eq_ev

eqCtLHS :: EqCt -> CanEqLHS
eqCtLHS = eq_lhs

data IrredCt = IrredCt
  { ir_ev :: CtEvidence
  , ir_reason :: CtIrredReason
  }

irredCtEvidence :: IrredCt -> CtEvidence
irredCtEvidence = ir_ev

irredCtPred :: IrredCt -> AnyPredKind
irredCtPred = ctEvPred . irredCtEvidence

instance Outputable IrredCt where
  ppr irred = ppr (CIrredCan irred)

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


mkNonCanonical :: CtEvidence -> Ct
mkNonCanonical = CNonCanonical

mkGivens :: CtLoc -> [KiEvVar AnyKiVar] -> [Ct]
mkGivens loc ev_vars = map mk ev_vars
  where mk ev_var = mkNonCanonical (CtGiven { ctev_evar = ev_var
                                            , ctev_pred = kiEvVarPred ev_var
                                            , ctev_loc = loc })

ctEvidence :: Ct -> CtEvidence
ctEvidence (CEqCan (KiEqCt { eq_ev = ev })) = ev
ctEvidence (CIrredCan (IrredCt { ir_ev = ev })) = ev
ctEvidence (CNonCanonical ev) = ev
ctEvidence (CRelCan (RelCt { rl_ev = ev })) = ev

updCtEvidence :: (CtEvidence -> CtEvidence) -> Ct -> Ct
updCtEvidence upd ct = case ct of
  CEqCan eq@(KiEqCt { eq_ev = ev }) -> CEqCan (eq { eq_ev = upd ev })
  CIrredCan ir@(IrredCt { ir_ev = ev }) -> CIrredCan (ir { ir_ev = upd ev })
  CNonCanonical ev -> CNonCanonical (upd ev)
  CRelCan rl@(RelCt { rl_ev = ev }) -> CRelCan (rl { rl_ev = upd ev })

ctLoc :: Ct -> CtLoc
ctLoc = ctEvLoc . ctEvidence

ctOrigin :: Ct -> CtOrigin
ctOrigin = ctLocOrigin . ctLoc

ctPred :: Ct -> AnyPredKind
ctPred ct = ctEvPred (ctEvidence ct)

ctKiEvVar :: Ct -> KiEvVar AnyKiVar
ctKiEvVar ct = ctEvKiEvVar (ctEvidence ct)

instance Outputable Ct where
  ppr ct = ppr (ctEvidence ct) <+> parens pp_short
    where
      pp_short = case ct of
                   CEqCan {} -> text "CEqCan"
                   CRelCan {} -> text "CRelCan"
                   CNonCanonical {} -> text "CNonCanonical"
                   CIrredCan (IrredCt { ir_reason = reason }) -> text "CIrredCan" <> ppr reason

instance Outputable EqCt where
  ppr (KiEqCt { eq_ev = ev }) = ppr ev

isGivenLoc :: CtLoc -> Bool
isGivenLoc loc = isGivenOrigin (ctLocOrigin loc)

{- *********************************************************************
*                                                                      *
                    CtEvidence
         The "flavor" of a canonical constraint
*                                                                      *
********************************************************************* -}

isWantedCt :: Ct -> Bool
isWantedCt = isWanted . ctEvidence

isGivenCt :: Ct -> Bool
isGivenCt = isGiven . ctEvidence

extendCtsList :: Cts -> [Ct] -> Cts
extendCtsList cts xs | null xs = cts
                     | otherwise = cts `unionBags` listToBag xs

andCts :: Cts -> Cts -> Cts
andCts = unionBags

consCts :: Ct -> Cts -> Cts
consCts = consBag

emptyCts :: Cts
emptyCts = emptyBag

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

mkImplicWC :: Bag Implication -> WantedConstraints
mkImplicWC implic = emptyWC { wc_impl = implic }

isEmptyWC :: WantedConstraints -> Bool
isEmptyWC (WC { wc_simple = f, wc_impl = i }) = isEmptyBag f && isEmptyBag i

isSolvedWC :: WantedConstraints -> Bool
isSolvedWC (WC simple impl) = isEmptyBag simple && allBag (isSolvedStatus . ic_status) impl

andWC :: WantedConstraints -> WantedConstraints -> WantedConstraints
andWC (WC { wc_simple = f1, wc_impl = i1 }) (WC { wc_simple = f2, wc_impl = i2 })
  = WC { wc_simple = f1 `unionBags` f2
       , wc_impl = i1 `unionBags` i2 }

addSimples :: WantedConstraints -> Cts -> WantedConstraints
addSimples wc cts = wc { wc_simple = wc_simple wc `unionBags` cts }

addImplics :: WantedConstraints -> Bag Implication -> WantedConstraints
addImplics wc implic = wc { wc_impl = wc_impl wc `unionBags` implic }

addInsols :: WantedConstraints -> Bag IrredCt -> WantedConstraints
addInsols wc insols = wc { wc_simple = wc_simple wc `unionBags` fmap CIrredCan insols }

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

isSolvedStatus :: ImplicStatus -> Bool
isSolvedStatus IC_Solved {} = True
isSolvedStatus _ = False

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

insolubleIrredCt :: IrredCt -> Bool
insolubleIrredCt (IrredCt { ir_ev = ev, ir_reason = reason })
  = isInsolubleReason reason

insolubleCt :: Ct -> Bool
insolubleCt (CIrredCan ir_ct) = insolubleIrredCt ir_ct
insolubleCt _ = False

instance Outputable WantedConstraints where
  ppr (WC { wc_simple = s, wc_impl = i })
    = text "WC" <+> braces (vcat [ ppr_bag (text "wc_simple") s
                                 , ppr_bag (text "wc_impl") i ])

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
  , ic_skols :: [TcKiVar] -- as in GHC (NO KiVars or MetaKiVars, just Skolem TcKiVars)
  , ic_given :: [KiEvVar AnyKiVar]
  , ic_given_eqs :: HasGivenEqs
  , ic_warn_inaccessible :: Bool
  , ic_env :: !CtLocEnv
  , ic_wanted :: WantedConstraints
  , ic_binds :: KiEvBindsVar
  , ic_status :: ImplicStatus
  , ic_need_inner :: MkVarSet (KiEvVar AnyKiVar)
  , ic_need_outer :: MkVarSet (KiEvVar AnyKiVar)
  }

implicationPrototype :: CtLocEnv -> Implication
implicationPrototype ct_loc_env = Implic
  { ic_tclvl = panic "newImplic:tclvl"
  , ic_binds = panic "newImplic:binds"
  , ic_info = panic "newImplic:info"
  , ic_skols = []
  , ic_given = []
  , ic_given_eqs = MaybeGivenEqs
  , ic_warn_inaccessible = panic "newImplic:warn_inaccessible"
  , ic_env = ct_loc_env
  , ic_wanted = emptyWC
  , ic_status = IC_Unsolved
  , ic_need_inner = emptyVarSet
  , ic_need_outer = emptyVarSet
  }

data ImplicStatus
  = IC_Solved { ics_dead :: [KiEvVar AnyKiVar] }
  | IC_Insoluble
  | IC_BadTelescope
  | IC_Unsolved

data HasGivenEqs
  = NoGivenEqs
  | LocalGivenEqs
  | MaybeGivenEqs
  deriving Eq

type UserGiven = Implication

getUserGivensFromImplics :: [Implication] -> [UserGiven]
getUserGivensFromImplics implics = reverse (filterOut (null . ic_given) implics)

instance Outputable Implication where
  ppr (Implic { ic_tclvl = tclvl
              , ic_skols = skols
              , ic_given = given
              , ic_given_eqs = given_eqs
              , ic_wanted = wanted
              , ic_status = status
              , ic_info = info })
    = hang (text "Implic" <+> lbrace)
      2 (sep [ text "TcLevel =" <+> ppr tclvl
             , text "Skolems =" <+> ppr skols
             , text "Given-eqs =" <+> ppr given_eqs
             , text "Status =" <+> ppr status
             , hang (text "Given =") 2 (pprKiEvVars given)
             , hang (text "Wanted =") 2 (ppr wanted)
             , pprSkolInfo info ] <+> rbrace)

instance Outputable ImplicStatus where
  ppr IC_Insoluble = text "Insoluble"
  ppr IC_BadTelescope = text "Bad telescope"
  ppr IC_Unsolved = text "Unsolved"
  ppr (IC_Solved dead) = text "Solved" <+> (braces (text "Dead givens =" <+> ppr dead))

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
checkImplicationInvariants implic = when debugIsOn (check_implic implic)

check_implic :: (HasCallStack, Applicative m) => Implication -> m ()
check_implic implic@(Implic { ic_tclvl = lvl, ic_info = skol_info, ic_skols = skols })
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
      | not (tv_lvl == lvl)
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
    go (SigSkol c1 t1 s1) (SigSkol c2 t2 s2) = c1 == c2 && panic "t1 `tcEqType` tc" && s1 == s2
    go (SigTypeSkol cx1) (SigTypeSkol cx2) = cx1 == cx2
    go (ForAllSkol _) (ForAllSkol _) = True
    go (TyLamTySkol ids1) (TyLamTySkol ids2)
      = equalLength ids1 ids2 && and (zipWith (==) ids1 ids2)
    go (InferSkol ids1) (InferSkol ids2)
      = equalLength ids1 ids2 && and (zipWith eq_pr ids1 ids2)
    go (UnifyForAllSkol t1) (UnifyForAllSkol t2) = panic "t1 `tcEqType` t2"
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

type AnyTyFV = TyFV (KiEvVar AnyKiVar) AnyKiVar
type AnyKiFV = KiFV AnyKiVar

fvsOfCt :: Ct -> AnyKiFV
fvsOfCt ct = fvsOfMonoKind $ ctPred ct

fvsOfCts :: Cts -> AnyKiFV
fvsOfCts = foldr (unionFV . fvsOfCt) emptyFV

varsOfWC :: WantedConstraints -> (MkVarSet (KiEvVar AnyKiVar), MkVarSet AnyKiVar)
varsOfWC wc = case fvVarAcc (fvsOfWC wc) of
  (_, tvs, _, kvs) -> (tvs, kvs)

varsOfWCList :: WantedConstraints -> ([KiEvVar AnyKiVar], [AnyKiVar])
varsOfWCList wc = case fvVarAcc (fvsOfWC wc) of
  (tvs, _, kvs, _) -> (tvs, kvs)

fvsOfWC :: WantedConstraints -> AnyTyFV
fvsOfWC (WC { wc_simple = simple, wc_impl = implic })
  = liftKiFV (fvsOfCts simple) `unionFV` fvsOfBag fvsOfImplic implic

fvsOfImplic :: Implication -> AnyTyFV
fvsOfImplic (Implic { ic_skols = skols, ic_given = givens, ic_wanted = wanted })
  | isEmptyWC wanted
  = emptyFV
  | otherwise
  = fvsKiVarBndrs (toAnyKiVar <$> skols)
    $ fvsVarBndrs givens
    $ fvsOfWC wanted

fvsOfBag :: (a -> AnyTyFV) -> Bag a -> AnyTyFV
fvsOfBag vs_of = foldr (unionFV . vs_of) emptyFV

{- *********************************************************************
*                                                                      *
            Pretty printing
*                                                                      *
********************************************************************* -}

pprKiEvVars :: [KiEvVar AnyKiVar] -> SDoc
pprKiEvVars ev_vars = vcat (map pprKiEvVarWithKind ev_vars)

pprKiEvVarTheta :: [KiEvVar AnyKiVar] -> SDoc
pprKiEvVarTheta ev_vars = pprTheta (map kiEvVarPred ev_vars)
  where
    pprTheta t = text "pprTheta NEEDS IMPLEMENTING" <+> ppr t

pprKiEvVarWithKind :: KiEvVar AnyKiVar -> SDoc
pprKiEvVarWithKind v = ppr v <+> colon <+> ppr (kiEvVarPred v)

{- *********************************************************************
*                                                                      *
            CtEvidence
*                                                                      *
********************************************************************* -}

data TcEvDest
  = EvVarDest (KiEvVar AnyKiVar)
  | HoleDest (KindCoercionHole AnyKiVar)

data CtEvidence
  = CtGiven
    { ctev_pred :: AnyPredKind
    , ctev_evar :: KiEvVar AnyKiVar
    , ctev_loc :: CtLoc }
  | CtWanted
    { ctev_pred :: AnyPredKind
    , ctev_dest :: TcEvDest 
    , ctev_loc :: CtLoc
    , ctev_rewriters :: RewriterSet
    }

ctEvPred :: CtEvidence -> AnyPredKind
ctEvPred = ctev_pred

ctEvLoc :: CtEvidence -> CtLoc
ctEvLoc = ctev_loc

ctEvRewriters :: CtEvidence -> RewriterSet
ctEvRewriters (CtWanted { ctev_rewriters = rewriters }) = rewriters
ctEvRewriters _ = emptyRewriterSet

ctEvType :: HasDebugCallStack => CtEvidence -> KiEvType
ctEvType ev@(CtWanted { ctev_dest = HoleDest _ }) = KindCoercion $ ctEvKiCoercion ev
ctEvType ev = kiEvVar (ctEvKiEvVar ev)

ctEvKiCoercion :: HasDebugCallStack => CtEvidence -> KindCoercion AnyKiVar
ctEvKiCoercion (CtGiven { ctev_pred = pred, ctev_evar = ev_var })
  = assertPpr (isKiEqPred pred)
    (vcat [ text "ctEvKiCoercion called on non-eq pred"
          , ppr pred, ppr ev_var ])
    $ mkKiCoVarCo ev_var
ctEvKiCoercion (CtWanted { ctev_dest = dest })
  | HoleDest hole <- dest
  = mkKiHoleCo hole
  | otherwise
  = panic "ctEvKiCoercion"

ctEvKiEvVar :: CtEvidence -> KiEvVar AnyKiVar
ctEvKiEvVar (CtWanted { ctev_dest = EvVarDest ev }) = ev
ctEvKiEvVar (CtWanted { ctev_dest = HoleDest h }) = coHoleCoVar h
ctEvKiEvVar (CtGiven { ctev_evar = ev }) = ev

arisesFromGivens :: Ct -> Bool
arisesFromGivens ct = isGivenCt ct || isGivenLoc (ctLoc ct)

setCtEvPredKind :: CtEvidence -> AnyPredKind -> CtEvidence
setCtEvPredKind old_ctev@(CtGiven { ctev_evar = ev }) new_pred
  = old_ctev { ctev_pred = new_pred
             , ctev_evar = setVarKind ev new_pred }
setCtEvPredKind old_ctev@(CtWanted { ctev_dest = dest }) new_pred
  = old_ctev { ctev_pred = new_pred, ctev_dest = new_dest }
  where
    new_dest = case dest of
      EvVarDest ev -> EvVarDest (setVarKind ev new_pred)
      HoleDest h -> HoleDest (setCoHoleKind h new_pred)

instance Outputable TcEvDest where
  ppr (HoleDest h) = text "hole" <> ppr h
  ppr (EvVarDest ev) = ppr ev

instance Outputable CtEvidence where
  ppr ev = ppr (ctEvFlavor ev)
           <+> braces (ppr (ctl_depth (ctEvLoc ev)))
           <> dcolon <+> ppr (ctEvPred ev)

isWanted :: CtEvidence -> Bool
isWanted (CtWanted {}) = True
isWanted _ = False

isGiven :: CtEvidence -> Bool
isGiven (CtGiven {}) = True
isGiven _ = False

{- *********************************************************************
*                                                                      *
           RewriterSet
*                                                                      *
********************************************************************* -}

type RWKiCoHole = KindCoercionHole AnyKiVar

newtype RewriterSet = RewriterSet (UniqSet RWKiCoHole)
  deriving newtype (Outputable, Semigroup, Monoid)

emptyRewriterSet :: RewriterSet
emptyRewriterSet = RewriterSet emptyUniqSet

unitRewriterSet :: RWKiCoHole -> RewriterSet
unitRewriterSet = coerce (unitUniqSet @RWKiCoHole)

unionRewriterSet :: RewriterSet -> RewriterSet -> RewriterSet
unionRewriterSet = coerce (unionUniqSets @RWKiCoHole)

isEmptyRewriterSet :: RewriterSet -> Bool
isEmptyRewriterSet = coerce (isEmptyUniqSet @RWKiCoHole)

addRewriter :: RewriterSet -> RWKiCoHole -> RewriterSet
addRewriter = coerce (addOneToUniqSet @RWKiCoHole)

rewriterSetFromCts :: Bag Ct -> RewriterSet
rewriterSetFromCts cts = foldr add emptyRewriterSet cts
  where
    add ct rw_set = case ctEvidence ct of
                      CtWanted { ctev_dest = HoleDest hole } -> rw_set `addRewriter` hole
                      _ -> rw_set

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
ctEvFlavor (CtGiven {}) = Given

eqCtFlavor :: EqCt -> CtFlavor
eqCtFlavor (KiEqCt { eq_ev = ev }) = ctEvFlavor ev

ctFlavor :: Ct -> CtFlavor
ctFlavor (CEqCan eq_ct) = eqCtFlavor eq_ct
ctFlavor ct = ctEvFlavor (ctEvidence ct)

canKiEqLHS_maybe :: AnyMonoKind -> Maybe CanEqLHS
canKiEqLHS_maybe xi
  | Just kv <- getKiVar_maybe xi
  = Just $ KiVarLHS kv
  | otherwise
  = Nothing

canKiEqLHSKind :: CanEqLHS -> AnyMonoKind
canKiEqLHSKind (KiVarLHS kv) = mkKiVarKi kv

eqCanEqLHS :: CanEqLHS -> CanEqLHS -> Bool
eqCanEqLHS (KiVarLHS kv1) (KiVarLHS kv2) = kv1 == kv2

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
