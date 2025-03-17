{-# LANGUAGE TypeApplications #-}

module CSlash.Tc.Solver.InertSet where

import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Origin
import CSlash.Tc.Solver.Types
import CSlash.Tc.Utils.TcType

import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Basic( SwapFlag(..) )

-- import GHC.Core.Reduction
-- import GHC.Core.Predicate
import CSlash.Core.Type.FVs
import CSlash.Core.Kind.FVs
import CSlash.Core.Kind.Compare
import qualified CSlash.Core.Type.Rep as Rep
-- import GHC.Core.Class( Class )
import CSlash.Core.TyCon
-- import GHC.Core.Class( classTyCon )
-- import GHC.Core.Unify

import CSlash.Utils.Misc ( partitionWith )
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Data.Maybe
import CSlash.Data.Bag

import Data.List.NonEmpty ( NonEmpty(..), (<|) )
import qualified Data.List.NonEmpty as NE
import Data.Function ( on )

import Control.Monad ( forM_ )

{- *********************************************************************
*                                                                      *
                  Worklists
*                                                                      *
********************************************************************* -}

data WorkList = WL
  { wl_eqs :: [Ct]
  , wl_rest :: [Ct]
  , wl_implics :: Bag Implication
  }

extendWorkListEq :: Ct -> WorkList -> WorkList
extendWorkListEq ct wl = wl { wl_eqs = ct : wl_eqs wl }

extendWorkListEqs :: Bag Ct -> WorkList -> WorkList
extendWorkListEqs eqs wl = wl { wl_eqs = foldr (:) (wl_eqs wl) eqs }

extendWorkListCt :: Ct -> WorkList -> WorkList
extendWorkListCt ct wl = case ctEvPred (ctEvidence ct) of
  KiEqPred {} -> extendWorkListEq ct wl

extendWorkListCts :: Cts -> WorkList -> WorkList
extendWorkListCts cts wl = foldr extendWorkListCt wl cts

emptyWorkList :: WorkList
emptyWorkList = WL { wl_eqs = [], wl_rest = [], wl_implics = emptyBag }

selectWorkItem :: WorkList -> Maybe (Ct, WorkList)
selectWorkItem wl@(WL { wl_eqs = eqs, wl_rest = rest })
  | ct : cts <- eqs = Just (ct, wl { wl_eqs = cts })
  | ct : cts <- rest = Just (ct, wl { wl_rest = cts })
  | otherwise = Nothing

instance Outputable WorkList where
  ppr (WL { wl_eqs = eqs, wl_rest = rest, wl_implics = implics })
    = text "WL" <+> (braces $
                     vcat [ ppUnless (null eqs)
                            $ text "Eqs =" <+> vcat (map ppr eqs)
                          , ppUnless (null rest)
                            $ text "Non-eqs" <+> vcat (map ppr rest)
                          , ppUnless (isEmptyBag implics)
                            $ ifPprDebug (text "Implics ="
                                          <+> vcat (map ppr (bagToList implics)))
                                         (text "(Implics omitted)") ])

{- *********************************************************************
*                                                                      *
                  InertSet
*                                                                      *
********************************************************************* -}

type CycleBreakerVarStack = NonEmpty (Bag (TcTyVar, TcType))

data InertSet = IS
  { inert_cans :: InertCans
  , inert_cycle_breakers :: CycleBreakerVarStack
  }

instance Outputable InertSet where
  ppr (IS { inert_cans = ics })
    = vcat [ ppr ics ]

emptyInertCans :: InertCans
emptyInertCans = IC { inert_eqs = emptyEqs
                    , inert_irreds = emptyBag
                    , inert_given_eq_lvl = topTcLevel
                    , inert_given_eqs = False
                    }

emptyInert :: InertSet
emptyInert = IS { inert_cans = emptyInertCans
                , inert_cycle_breakers = emptyBag :| []
                }

{- *********************************************************************
*                                                                      *
                InertCans: the canonical inerts
*                                                                      *
********************************************************************* -}

data InertCans = IC
  { inert_eqs :: InertEqs
  , inert_irreds :: InertIrreds
  , inert_given_eq_lvl :: TcLevel
  , inert_given_eqs :: Bool
  }

type InertEqs = DVarEnv EqualCtList
type InertIrreds = Bag IrredCt

instance Outputable InertCans where
  ppr (IC { inert_eqs = eqs
          , inert_irreds = irreds
          , inert_given_eq_lvl = ge_lvl
          , inert_given_eqs = given_eqs })
    = braces $ vcat
      [ ppUnless (isEmptyDVarEnv eqs)
        $ text "Equalities ="
        <+> pprBag (foldEqs consBag eqs emptyBag)
      , ppUnless (isEmptyBag irreds)
        $ text "Irreds =" <+> pprBag irreds
      , text "Innermost given equalities =" <+> ppr ge_lvl
      , text "Given eqs at this level =" <+> ppr given_eqs
      ]

{- *********************************************************************
*                                                                      *
                   Inert equalities
*                                                                      *
********************************************************************* -}

emptyEqs :: InertEqs
emptyEqs = emptyDVarEnv

addEqToCans :: TcLevel -> EqCt -> InertCans -> InertCans
addEqToCans tc_lvl eq_ct@(KiEqCt { eq_lhs = lhs }) ics@(IC { inert_eqs = eqs })
  = updGivenEqs tc_lvl (CEqCan eq_ct)
    $ case lhs of
        KiVarLHS kv -> ics { inert_eqs = addEq eqs kv eq_ct }

addEq :: InertEqs -> TcVar -> EqCt -> InertEqs
addEq old_eqs v ct
  = extendDVarEnv_C add_eq old_eqs v [ct]
  where
    add_eq old_eqs _ = addToEqualCtList ct old_eqs

findKiEqs :: InertCans -> KindVar -> [EqCt]
findKiEqs icans kv = concat @Maybe (lookupDVarEnv (inert_eqs icans) kv)

findEq :: InertCans -> CanEqLHS -> [EqCt]
findEq icans (KiVarLHS kv) = findKiEqs icans kv

foldEqs :: (EqCt -> b -> b) -> InertEqs -> b -> b
foldEqs k eqs z = foldDVarEnv (\cts z -> foldr k z cts) z eqs

{- *********************************************************************
*                                                                      *
                   Inert Irreds
*                                                                      *
********************************************************************* -}

addIrredToCans :: TcLevel -> IrredCt -> InertCans -> InertCans
addIrredToCans tc_lvl irred ics
  = updGivenEqs tc_lvl (CIrredCan irred)
    $ updIrreds (addIrred irred) ics

addIrreds :: [IrredCt] -> InertIrreds -> InertIrreds
addIrreds extras irreds
  | null extras = irreds
  | otherwise = irreds `unionBags` listToBag extras

addIrred :: IrredCt -> InertIrreds -> InertIrreds
addIrred extra irreds = irreds `snocBag` extra

updIrreds :: (InertIrreds -> InertIrreds) -> InertCans -> InertCans
updIrreds upd ics = ics { inert_irreds = upd (inert_irreds ics) }

findMatchingIrreds :: InertIrreds -> CtEvidence -> (Bag (IrredCt, SwapFlag), InertIrreds)
findMatchingIrreds irreds ev = case ctEvPred ev of
  KiEqPred lki1 rki1 -> partitionBagWith (match_eq lki1 rki1) irreds
  where
    match_eq lki1 rki1 irred = case irredCtPred irred of
      KiEqPred lki2 rki2
        | Just swap <- match_eq_help lki1 rki1 lki2 rki2
          -> Left (irred, swap)
        | otherwise
          -> Right irred

    match_eq_help lki1 rki1 lki2 rki2
      | lki1 `tcEqKind` lki2, rki1 `tcEqKind` rki2
      = Just NotSwapped
      | lki1 `tcEqKind` rki2, rki1 `tcEqKind` lki2
      = Just IsSwapped
      | otherwise
      = Nothing

{- *********************************************************************
*                                                                      *
    Adding to and removing from the inert set
*                                                                      *
********************************************************************* -}

updGivenEqs :: TcLevel -> Ct -> InertCans -> InertCans
updGivenEqs tclvl ct inerts@(IC { inert_given_eq_lvl = ge_lvl })
  | not (isGivenCt ct) = inerts
  | not_equality ct = inerts
  | otherwise = inerts { inert_given_eq_lvl = ge_lvl'
                       , inert_given_eqs = True }
  where
    ge_lvl' | mentionsOuterVar tclvl (ctEvidence ct)
            = tclvl
            | otherwise
            = ge_lvl

    not_equality (CEqCan (KiEqCt { eq_lhs = KiVarLHS kv })) = not (isOuterKiVar tclvl kv)
    not_equality (CEqCan _) = panic "updGivenEqs"
    not_equality _ = False

data KickOutSpec
  = KOAfterUnify VarSet
  | KOAfterAdding CanEqLHS

kickOutRewritableLHS :: KickOutSpec -> CtFlavor -> InertCans -> (Cts, InertCans)
kickOutRewritableLHS _ _ ics@(IC _ _ _ _) = panic "kickOutRewritableLHS"

{- *********************************************************************
*                                                                      *
                 Queries
*                                                                      *
********************************************************************* -}

mentionsOuterVar :: TcLevel -> CtEvidence -> Bool
mentionsOuterVar tclvl ev
  | Just (ki1, ki2) <- ctEvPredKind_maybe ev
  = anyFreeVarsOfKind (isOuterKiVar tclvl) ki1
    || anyFreeVarsOfKind (isOuterKiVar tclvl) ki2
  | otherwise
  = panic "mentionsOuterVar"

isOuterKiVar :: TcLevel -> KindVar -> Bool
isOuterKiVar tclvl kv
  | isKiVar kv = assertPpr (not (isTouchableMetaKiVar tclvl kv)) (ppr kv <+> ppr tclvl)
                 $ tclvl `strictlyDeeperThan` tcKiVarLevel kv
  | otherwise = False

{- *********************************************************************
*                                                                      *
    Cycle breakers
*                                                                      *
********************************************************************* -}

pushCycleBreakerVarStack :: CycleBreakerVarStack -> CycleBreakerVarStack
pushCycleBreakerVarStack = (emptyBag <|)

forAllCycleBreakerBindings_
  :: Monad m => CycleBreakerVarStack -> (TcTyVar -> TcType -> m ()) -> m ()
forAllCycleBreakerBindings_ (top_env :| _) action
  = forM_ top_env (uncurry action)
{-# INLINABLE forAllCycleBreakerBindings_ #-}

{- *********************************************************************
*                                                                      *
         Solving one from another
*                                                                      *
********************************************************************* -}

data InteractResult
  = KeepInert
  | KeepWork

instance Outputable InteractResult where
  ppr KeepInert = text "keep inert"
  ppr KeepWork = text "keep work-item"

solveOneFromTheOther :: Ct -> Ct -> InteractResult
solveOneFromTheOther ct_i ct_w
  | CtWanted {} <- ev_w
  = case ev_i of
      --CtGiven {} -> KeepInert
      CtWanted {}
        | ((<) `on` ctLocSpan) loc_i loc_w -> KeepInert
        | otherwise -> KeepWork
  | CtWanted {} <- ev_i
  = KeepWork
  | lvl_i == lvl_w
  = same_level_strategy
  | otherwise
  = different_level_strategy

  where
    ev_i = ctEvidence ct_i
    ev_w = ctEvidence ct_w

    pred = ctEvPred ev_i

    loc_i = ctEvLoc ev_i
    loc_w = ctEvLoc ev_w
    orig_i = ctLocOrigin loc_i
    orig_w = ctLocOrigin loc_w
    lvl_i = ctLocLevel loc_i
    lvl_w = ctLocLevel loc_w

    different_level_strategy = if lvl_w > lvl_i then KeepInert else KeepWork

    same_level_strategy = case (orig_i, orig_w) of
      (KindEqOrigin {}, KindEqOrigin {}) -> KeepInert
