{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
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
import CSlash.Core.Predicate
import CSlash.Core.Type.FVs
import CSlash.Core.Kind.FVs
import CSlash.Core.Kind
import CSlash.Core.Kind.Subst
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
  , wl_rw_eqs :: [Ct]
  , wl_rest :: [Ct]
  , wl_implics :: Bag Implication
  }

extendWorkListEq :: RewriterSet -> Ct -> WorkList -> WorkList
extendWorkListEq rewriters ct wl
  | isEmptyRewriterSet rewriters
  = wl { wl_eqs = ct : wl_eqs wl }
  | otherwise
  = wl { wl_rw_eqs = ct : wl_rw_eqs wl }

extendWorkListEqs :: RewriterSet -> Bag Ct -> WorkList -> WorkList
extendWorkListEqs rewriters eqs wl
  | isEmptyRewriterSet rewriters
  = wl { wl_eqs = foldr (:) (wl_eqs wl) eqs }
  | otherwise
  = wl { wl_rw_eqs = foldr (:) (wl_rw_eqs wl) eqs }

extendWorkListNonEq :: Ct -> WorkList -> WorkList
extendWorkListNonEq ct wl = wl { wl_rest = ct : wl_rest wl }

extendWorkListCt :: Ct -> WorkList -> WorkList
extendWorkListCt ct wl = case classifyPredKind (ctEvPred ev) of
  EqPred {} -> extendWorkListEq rewriters ct wl
  _ -> extendWorkListNonEq ct wl
  where
    ev = ctEvidence ct
    rewriters = ctEvRewriters ev  

extendWorkListCts :: Cts -> WorkList -> WorkList
extendWorkListCts cts wl = foldr extendWorkListCt wl cts

emptyWorkList :: WorkList
emptyWorkList = WL { wl_eqs = [], wl_rw_eqs = [], wl_rest = [], wl_implics = emptyBag }

selectWorkItem :: WorkList -> Maybe (Ct, WorkList)
selectWorkItem wl@(WL { wl_eqs = eqs, wl_rw_eqs = rw_eqs, wl_rest = rest })
  | ct : cts <- eqs = Just (ct, wl { wl_eqs = cts })
  | ct:cts <- rw_eqs = Just (ct, wl { wl_rw_eqs = cts })
  | ct : cts <- rest = Just (ct, wl { wl_rest = cts })
  | otherwise = Nothing

instance Outputable WorkList where
  ppr (WL { wl_eqs = eqs, wl_rw_eqs = rw_eqs, wl_rest = rest, wl_implics = implics })
    = text "WL" <+> (braces $
                     vcat [ ppUnless (null eqs)
                            $ text "Eqs =" <+> vcat (map ppr eqs)
                          , ppUnless (null rw_eqs)
                            $ text "RwEqs =" <+> vcat (map ppr rw_eqs)
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
  , inert_solved_rels :: RelMap RelCt
  }

instance Outputable InertSet where
  ppr (IS { inert_cans = ics, inert_solved_rels = solved_rels })
    = vcat [ ppr ics
           , ppUnless (null rels)
           $ text "Solved rels =" <+> vcat (map ppr rels) ]
    where
      rels = bagToList $ relsToBag solved_rels

emptyInertCans :: InertCans
emptyInertCans = IC { inert_eqs = emptyEqs
                    , inert_rels = emptyRelMap
                    , inert_irreds = emptyBag
                    , inert_given_eq_lvl = topTcLevel
                    , inert_given_eqs = False
                    }

emptyInert :: InertSet
emptyInert = IS { inert_cans = emptyInertCans
                , inert_cycle_breakers = emptyBag :| []
                , inert_solved_rels = emptyRelMap
                }

{- *********************************************************************
*                                                                      *
                InertCans: the canonical inerts
*                                                                      *
********************************************************************* -}

data InertCans = IC
  { inert_eqs :: InertEqs
  , inert_rels :: RelMap RelCt
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
        <+> pprBag (foldKiEqs consBag eqs emptyBag)
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

foldKiEqs :: (EqCt -> b -> b) -> InertEqs -> b -> b
foldKiEqs k eqs z = foldDVarEnv (\cts z -> foldr k z cts) z eqs

findKiEqs :: InertCans -> KindVar -> [EqCt]
findKiEqs icans kv = concat @Maybe (lookupDVarEnv (inert_eqs icans) kv)

findEq :: InertCans -> CanEqLHS -> [EqCt]
findEq icans (KiVarLHS kv) = findKiEqs icans kv

{-# INLINE partition_eqs_container #-}
partition_eqs_container
  :: forall container
   . container
  -> (forall b. (EqCt -> b -> b) -> container -> b -> b)
  -> (EqCt -> container -> container)
  -> (EqCt -> Bool)
  -> container
  -> ([EqCt], container)
partition_eqs_container empty_container fold_container extend_container pred orig_inerts
  = fold_container folder orig_inerts ([], empty_container)
  where
    folder :: EqCt -> ([EqCt], container) -> ([EqCt], container)
    folder eq_ct (acc_true, acc_false)
      | pred eq_ct = (eq_ct : acc_true, acc_false)
      | otherwise = (acc_true, extend_container eq_ct acc_false)

partitionInertEqs :: (EqCt -> Bool) -> InertEqs -> ([EqCt], InertEqs)
partitionInertEqs = partition_eqs_container emptyEqs foldKiEqs addInertEqs

addInertEqs :: EqCt -> InertEqs -> InertEqs
addInertEqs  eq_ct@(KiEqCt { eq_lhs = KiVarLHS kv }) eqs = addEq eqs kv eq_ct

{- *********************************************************************
*                                                                      *
                   Inert Rels
*                                                                      *
********************************************************************* -}

updRels :: (RelMap RelCt -> RelMap RelCt) -> InertCans -> InertCans
updRels upd ics = ics { inert_rels = upd (inert_rels ics) }

delRel :: RelCt -> RelMap a -> RelMap a
delRel (RelCt { rl_kc = kc, rl_ki1 = k1, rl_ki2 = k2 }) m = delKcApp m kc k1 k2

addRel :: RelCt -> RelMap RelCt -> RelMap RelCt
addRel item@(RelCt { rl_kc = kc, rl_ki1 = k1, rl_ki2 = k2 }) rm
  = insertKcApp rm kc k1 k2 item

addSolvedRel :: RelCt -> RelMap RelCt -> RelMap RelCt
addSolvedRel item@(RelCt { rl_kc = kc, rl_ki1 = k1, rl_ki2 = k2 }) rm
  = insertKcApp rm kc k1 k2 item

partitionRels :: (RelCt -> Bool) -> RelMap RelCt -> (Bag RelCt, RelMap RelCt)
partitionRels f m = foldKcAppMap k m (emptyBag, emptyRelMap)
  where
    k ct (yeses, noes) | f ct = (ct `consBag` yeses, noes)
                       | otherwise = (yeses, addRel ct noes)

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
findMatchingIrreds irreds ev 
  | EqPred lki1 rki1 <- classifyPredKind pred
  = partitionBagWith (match_eq lki1 rki1) irreds
  | otherwise
  = partitionBagWith match_non_eq irreds
  where
    pred = ctEvPred ev

    match_non_eq irred
      | irredCtPred irred `tcEqMonoKind` pred = Left (irred, NotSwapped)
      | otherwise = Right irred

    match_eq lki1 rki1 irred
      | EqPred lki2 rki2 <- classifyPredKind (irredCtPred irred)
      , Just swap <- match_eq_help lki1 rki1 lki2 rki2
      = Left (irred, swap)
      | otherwise
      = Right irred

    match_eq_help lki1 rki1 lki2 rki2
      | lki1 `tcEqMonoKind` lki2, rki1 `tcEqMonoKind` rki2
      = Just NotSwapped
      | lki1 `tcEqMonoKind` rki2, rki1 `tcEqMonoKind` lki2
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
kickOutRewritableLHS ko_spec new_f ics@(IC { inert_eqs = kv_eqs
                                           , inert_rels = relmap
                                           , inert_irreds = irreds })
  = (kicked_out, inert_cans_in)
  where
    inert_cans_in = ics { inert_eqs = kv_eqs_in
                        , inert_rels = rels_in
                        , inert_irreds = irs_in }

    kicked_out :: Cts
    kicked_out = (fmap CRelCan rels_out `andCts` fmap CIrredCan irs_out)
                 `extendCtsList` fmap CEqCan kv_eqs_out

    (kv_eqs_out, kv_eqs_in) = partitionInertEqs kick_out_eq kv_eqs
    (rels_out, rels_in) = partitionRels (kick_out_ct . CRelCan) relmap
    (irs_out, irs_in) = partitionBag (kick_out_ct . CIrredCan) irreds

    f_kv_can_rewrite_ki :: (KindVar -> Bool) -> MonoKind -> Bool
    f_kv_can_rewrite_ki = anyRewritableKiVar 

    {-# INLINE f_can_rewrite_ki #-}
    f_can_rewrite_ki :: MonoKind -> Bool
    f_can_rewrite_ki = case ko_spec of
      KOAfterUnify kvs -> f_kv_can_rewrite_ki (`elemVarSet` kvs)
      KOAfterAdding (KiVarLHS kv) -> f_kv_can_rewrite_ki (== kv)

    f_may_rewrite f = new_f `eqCanRewriteF` f

    kick_out_ct ct = f_may_rewrite (ctFlavor ct) && f_can_rewrite_ki (ctPred ct)

    kick_out_eq (KiEqCt { eq_lhs = lhs, eq_rhs = rhs_ki, eq_ev = ev })
      | not (f_may_rewrite f)
      = False
      | KiVarLHS _ <- lhs
      , f `eqCanRewriteF` new_f
      = False
      | f_can_rewrite_ki (canKiEqLHSKind lhs)
      = True
      | kick_out_for_inertness = True
      | kick_out_for_completeness = True
      | otherwise = False
      where
        f = ctEvFlavor ev
        kick_out_for_inertness = (f `eqCanRewriteF` f) && f_can_rewrite_ki rhs_ki
        kick_out_for_completeness = is_new_lhs_ki rhs_ki

    is_new_lhs_ki = case ko_spec of
      KOAfterUnify vs -> is_kivar_ki_for vs
      KOAfterAdding lhs -> (`eqMonoKind` canKiEqLHSKind lhs)

    is_kivar_ki_for vs ki = case getKiVarMono_maybe ki of
                              Nothing -> False
                              Just kv -> kv `elemVarSet` vs

{- *********************************************************************
*                                                                      *
                 Queries
*                                                                      *
********************************************************************* -}

mentionsOuterVar :: TcLevel -> CtEvidence -> Bool
mentionsOuterVar tclvl ev = anyFreeVarsOfMonoKind (isOuterKiVar tclvl) $ ctEvPred ev

isOuterKiVar :: TcLevel -> KindVar -> Bool
isOuterKiVar tclvl kv
  | isKiVar kv = assertPpr (not (isTouchableMetaKiVar tclvl kv)) (ppr kv <+> ppr tclvl)
                 $ tclvl `strictlyDeeperThan` tcKiVarLevel kv
  | otherwise = False

noMatchableGivenRels :: InertSet -> CtLoc -> KiCon -> MonoKind -> MonoKind -> Bool
noMatchableGivenRels inerts@(IS { inert_cans = inert_cans }) loc_w kc k1 k2
  = not $ anyBag matchable_given
    $ findRelsByRel (inert_rels inert_cans) kc
  where
    pred_w = mkRelPred kc k1 k2

    matchable_given :: RelCt -> Bool
    matchable_given (RelCt { rl_ev = ev })
      | CtGiven { ctev_loc = loc_g, ctev_pred = pred_g } <- ev
      = isJust $ mightEqualLater inerts pred_g loc_g pred_w loc_w
      | otherwise
      = False

mightEqualLater :: InertSet -> TcPredKind -> CtLoc -> TcPredKind -> CtLoc -> Maybe Subst
mightEqualLater inert_set given_pred given_loc wanted_pred wanted_loc
  = panic "mightEqualLater"

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
      CtGiven {} -> KeepInert
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
      _ -> KeepInert
      
