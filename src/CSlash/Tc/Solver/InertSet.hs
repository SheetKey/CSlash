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
import CSlash.Core.Unify

import CSlash.Utils.Misc ( partitionWith )
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Trace
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
  { wl_kicos :: [KiCt]
  , wl_rw_kicos :: [KiCt]
  , wl_ki_rest :: [KiCt]
  , wl_ki_implics :: Bag KiImplication
  , wl_tyeqs :: [TyCt]
  , wl_rw_tyeqs :: [TyCt]
  , wl_ty_rest :: [TyCt]
  , wl_ty_implics :: Bag TyImplication
  }

extendWorkListKiCo :: KiRewriterSet -> KiCt -> WorkList -> WorkList
extendWorkListKiCo rewriters ct wl
  | isEmptyKiRewriterSet rewriters
  = wl { wl_kicos = ct : wl_kicos wl }
  | otherwise
  = wl { wl_rw_kicos = ct : wl_rw_kicos wl }

extendWorkListTyEq :: TyRewriterSet -> TyCt -> WorkList -> WorkList
extendWorkListTyEq rewriters ct wl
  | isEmptyTyRewriterSet rewriters
  = wl { wl_tyeqs = ct : wl_tyeqs wl }
  | otherwise
  = wl { wl_rw_tyeqs = ct : wl_rw_tyeqs wl }

extendWorkListKiCos :: KiRewriterSet -> Bag KiCt -> WorkList -> WorkList
extendWorkListKiCos rewriters kicos wl
  | isEmptyKiRewriterSet rewriters
  = wl { wl_kicos = foldr (:) (wl_kicos wl) kicos }
  | otherwise
  = wl { wl_rw_kicos = foldr (:) (wl_rw_kicos wl) kicos }

extendWorkListNonKiCo :: KiCt -> WorkList -> WorkList
extendWorkListNonKiCo ct wl = wl { wl_ki_rest = ct : wl_ki_rest wl }

extendWorkListNonTyEq :: TyCt -> WorkList -> WorkList
extendWorkListNonTyEq ct wl = wl { wl_ty_rest = ct : wl_ty_rest wl }

extendWorkListKiCt :: KiCt -> WorkList -> WorkList
extendWorkListKiCt ct wl = case classifyPredKind (ctKiEvPred ev) of
  KiCoPred {} -> extendWorkListKiCo rewriters ct wl
  _ -> extendWorkListNonKiCo ct wl
  where
    ev = ctKiEvidence ct
    rewriters = ctKiEvRewriters ev  

extendWorkListTyCt :: TyCt -> WorkList -> WorkList
extendWorkListTyCt ct wl = case classifyPredType (ctTyEvPred ev) of
  TyEqPred {} -> extendWorkListTyEq rewriters ct wl
  _ -> extendWorkListNonTyEq ct wl
  where
    ev = ctTyEvidence ct
    rewriters = ctTyEvRewriters ev  

extendWorkListKiCts :: KiCts -> WorkList -> WorkList
extendWorkListKiCts cts wl = foldr extendWorkListKiCt wl cts

extendWorkListTyCts :: TyCts -> WorkList -> WorkList
extendWorkListTyCts cts wl = foldr extendWorkListTyCt wl cts

emptyWorkList :: WorkList
emptyWorkList = WL { wl_kicos = [], wl_rw_kicos = [], wl_ki_rest = [], wl_ki_implics = emptyBag
                   , wl_tyeqs = [], wl_rw_tyeqs = [], wl_ty_rest = [], wl_ty_implics = emptyBag }

selectWorkItem :: WorkList -> Maybe (Either TyCt KiCt, WorkList)
selectWorkItem wl@(WL { wl_kicos = kicos, wl_rw_kicos = rw_kicos, wl_ki_rest = ki_rest
                      , wl_tyeqs = tyeqs, wl_rw_tyeqs = rw_tyeqs, wl_ty_rest = ty_rest })
  | ct : cts <- kicos = Just (Right ct, wl { wl_kicos = cts })
  | ct : cts <- rw_kicos = Just (Right ct, wl { wl_rw_kicos = cts })
  | ct : cts <- ki_rest = Just (Right ct, wl { wl_ki_rest = cts })
  | ct : cts <- tyeqs = Just (Left ct, wl { wl_tyeqs = cts })
  | ct : cts <- rw_tyeqs = Just (Left ct, wl { wl_rw_tyeqs = cts })
  | ct : cts <- ty_rest = Just (Left ct, wl { wl_ty_rest = cts })
  | otherwise = Nothing

instance Outputable WorkList where
  ppr (WL { wl_kicos = kicos, wl_rw_kicos = rw_kicos
          , wl_ki_rest = ki_rest, wl_ki_implics = ki_implics
          , wl_tyeqs = tyeqs, wl_rw_tyeqs = rw_tyeqs
          , wl_ty_rest = ty_rest, wl_ty_implics = ty_implics })
    = text "WL" <+> (braces $
                     vcat [ ppUnless (null kicos)
                            $ text "KiCos =" <+> vcat (map ppr kicos)
                          , ppUnless (null rw_kicos)
                            $ text "RwKiCos =" <+> vcat (map ppr rw_kicos)
                          , ppUnless (null ki_rest)
                            $ text "Non-kicos" <+> vcat (map ppr ki_rest)
                          , ppUnless (isEmptyBag ki_implics)
                            $ ifPprDebug (text "KiImplics ="
                                          <+> vcat (map ppr (bagToList ki_implics)))
                                         (text "(KiImplics omitted)")
                          , ppUnless (null tyeqs)
                            $ text "TyEqs =" <+> vcat (map ppr tyeqs)
                          , ppUnless (null rw_tyeqs)
                            $ text "RwTyEqs =" <+> vcat (map ppr rw_tyeqs)
                          , ppUnless (null ty_rest)
                            $ text "Non-tyeqs" <+> vcat (map ppr ty_rest)
                          , ppUnless (isEmptyBag ty_implics)
                            $ ifPprDebug (text "TyImplics ="
                                          <+> vcat (map ppr (bagToList ty_implics)))
                                         (text "(TyImplics omitted")
                          ])

{- *********************************************************************
*                                                                      *
                  InertSet
*                                                                      *
********************************************************************* -}

type CycleBreakerVarStack = NonEmpty (Bag (AnyTyVar AnyKiVar, AnyType))

data InertKiSet = IKS
  { inert_ki_cans :: InertKiCans
  -- , inert_cycle_breakers :: CycleBreakerVarStack
  }

data InertTySet = ITS
  { inert_ty_cans :: InertTyCans
  -- , inert_cycle_breakers :: CycleBreakerVarStack
  }

instance Outputable InertKiSet where
  ppr (IKS { inert_ki_cans = ics })
    = vcat [ ppr ics ]

instance Outputable InertTySet where
  ppr (ITS { inert_ty_cans = ics })
    = vcat [ ppr ics ]

class InertCans ic where
  emptyInertCans :: ic

class InertSet is where
  emptyInert :: is

instance InertCans InertKiCans where
  emptyInertCans = IKC { inert_kicos = emptyKiCos
                       , inert_ki_irreds = emptyBag
                       , inert_given_kico_lvl = topTcLevel
                       , inert_given_kicos = False
                       }

instance InertCans InertTyCans where
  emptyInertCans = ITC { inert_tyeqs = emptyTyEqs
                       , inert_ty_irreds = emptyBag
                       , inert_given_tyeq_lvl = topTcLevel
                       , inert_given_tyeqs = False
                       }

instance InertSet InertKiSet where
  emptyInert = IKS { inert_ki_cans = emptyInertCans }

instance InertSet InertTySet where
  emptyInert = ITS { inert_ty_cans = emptyInertCans }

{- *********************************************************************
*                                                                      *
                InertCans: the canonical inerts
*                                                                      *
********************************************************************* -}

data InertKiCans = IKC
  { inert_kicos :: InertKiCos
  , inert_ki_irreds :: InertKiIrreds
  , inert_given_kico_lvl :: TcLevel
  , inert_given_kicos :: Bool
  }

data InertTyCans = ITC
  { inert_tyeqs :: InertTyEqs
  , inert_ty_irreds :: InertTyIrreds
  , inert_given_tyeq_lvl :: TcLevel
  , inert_given_tyeqs :: Bool
  }

type InertKiCos = MkDVarEnv AnyKiVar KiCoCtList
type InertKiIrreds = Bag IrredKiCt

type InertTyEqs = MkDVarEnv (AnyTyVar AnyKiVar) TyEqCtList
type InertTyIrreds = Bag IrredTyCt

instance Outputable InertKiCans where
  ppr (IKC { inert_kicos = kicos
          , inert_ki_irreds = irreds
          , inert_given_kico_lvl = kc_lvl
          , inert_given_kicos = given_kicos })
    = braces $ vcat
      [ ppUnless (isEmptyDVarEnv kicos)
        $ text "KindCoercions ="
        <+> pprBag (foldKiCos consBag kicos emptyBag)
      , ppUnless (isEmptyBag irreds)
        $ text "KiIrreds =" <+> pprBag irreds
      , text "Innermost given kicos =" <+> ppr kc_lvl
      , text "Given kicos at this level =" <+> ppr given_kicos
      ]

instance Outputable InertTyCans where
  ppr (ITC { inert_tyeqs = tyeqs
           , inert_ty_irreds = irreds
           , inert_given_tyeq_lvl = tc_lvl
           , inert_given_tyeqs = given_tyeqs })
    = braces $ vcat
      [ ppUnless (isEmptyDVarEnv tyeqs)
        $ text "TypeCoercions ="
        <+> pprBag (foldTyEqs consBag tyeqs emptyBag)
      , ppUnless (isEmptyBag irreds)
        $ text "TyIrreds =" <+> pprBag irreds
      , text "Innermost given tyeqs =" <+> ppr tc_lvl
      , text "Given tyeqs at this level =" <+> ppr given_tyeqs
      ]

{- *********************************************************************
*                                                                      *
                   Inert equalities
*                                                                      *
********************************************************************* -}

emptyKiCos :: InertKiCos
emptyKiCos = emptyDVarEnv

emptyTyEqs :: InertTyEqs
emptyTyEqs = emptyDVarEnv

addKiCoToCans :: TcLevel -> KiCoCt -> InertKiCans -> InertKiCans
addKiCoToCans tc_lvl kico_ct@(KiCoCt { kc_lhs = lhs }) ics@(IKC { inert_kicos = kicos })
  = updGivenKiCos tc_lvl (CKiCoCan kico_ct)
    $ case lhs of
        KiVarLHS kv -> ics { inert_kicos = addKiCo kicos kv kico_ct }

addKiCo :: InertKiCos -> AnyKiVar -> KiCoCt -> InertKiCos
addKiCo old_kicos v ct
  = extendDVarEnv_C add_kico old_kicos v [ct]
  where
    add_kico old_kicos _ = addToKiCoCtList ct old_kicos

foldKiCos :: (KiCoCt -> b -> b) -> InertKiCos -> b -> b
foldKiCos k kicos z = foldDVarEnv (\cts z -> foldr k z cts) z kicos

foldTyEqs :: (TyEqCt -> b -> b) -> InertTyEqs -> b -> b
foldTyEqs k eqs z = foldDVarEnv (\cts z -> foldr k z cts) z eqs

findKiCos :: InertKiCans -> AnyKiVar -> [KiCoCt]
findKiCos icans kv = concat @Maybe (lookupDVarEnv (inert_kicos icans) kv)

findKiCo :: InertKiCans -> CanKiCoLHS -> [KiCoCt]
findKiCo icans (KiVarLHS kv) = findKiCos icans kv

{-# INLINE partition_kicos_container #-}
partition_kicos_container
  :: forall container
   . container
  -> (forall b. (KiCoCt -> b -> b) -> container -> b -> b)
  -> (KiCoCt -> container -> container)
  -> (KiCoCt -> Bool)
  -> container
  -> ([KiCoCt], container)
partition_kicos_container empty_container fold_container extend_container pred orig_inerts
  = fold_container folder orig_inerts ([], empty_container)
  where
    folder :: KiCoCt -> ([KiCoCt], container) -> ([KiCoCt], container)
    folder kico_ct (acc_true, acc_false)
      | pred kico_ct = (kico_ct : acc_true, acc_false)
      | otherwise = (acc_true, extend_container kico_ct acc_false)

partitionInertKiCos :: (KiCoCt -> Bool) -> InertKiCos -> ([KiCoCt], InertKiCos)
partitionInertKiCos = partition_kicos_container emptyKiCos foldKiCos addInertKiCos

addInertKiCos :: KiCoCt -> InertKiCos -> InertKiCos
addInertKiCos kico_ct@(KiCoCt { kc_lhs = KiVarLHS kv }) kicos = addKiCo kicos kv kico_ct

{- *********************************************************************
*                                                                      *
                   Inert Rels
*                                                                      *
********************************************************************* -}

-- updRels :: (RelMap RelCt -> RelMap RelCt) -> InertCans -> InertCans
-- updRels upd ics = ics { inert_rels = upd (inert_rels ics) }

-- delRel :: RelCt -> RelMap a -> RelMap a
-- delRel (RelCt { rl_kc = kc, rl_ki1 = k1, rl_ki2 = k2 }) m = delKcApp m kc k1 k2

-- addRel :: RelCt -> RelMap RelCt -> RelMap RelCt
-- addRel item@(RelCt { rl_kc = kc, rl_ki1 = k1, rl_ki2 = k2 }) rm
--   = insertKcApp rm kc k1 k2 item

-- addSolvedRel :: RelCt -> RelMap RelCt -> RelMap RelCt
-- addSolvedRel item@(RelCt { rl_kc = kc, rl_ki1 = k1, rl_ki2 = k2 }) rm
--   = insertKcApp rm kc k1 k2 item

-- partitionRels :: (RelCt -> Bool) -> RelMap RelCt -> (Bag RelCt, RelMap RelCt)
-- partitionRels f m = foldKcAppMap k m (emptyBag, emptyRelMap)
--   where
--     k ct (yeses, noes) | f ct = (ct `consBag` yeses, noes)
--                        | otherwise = (yeses, addRel ct noes)

{- *********************************************************************
*                                                                      *
                   Inert Irreds
*                                                                      *
********************************************************************* -}

addIrredToCans :: TcLevel -> IrredKiCt -> InertKiCans -> InertKiCans
addIrredToCans tc_lvl irred ics
  = updGivenKiCos tc_lvl (CIrredCanKi irred)
    $ updIrreds (addIrred irred) ics

addIrreds :: [IrredKiCt] -> InertKiIrreds -> InertKiIrreds
addIrreds extras irreds
  | null extras = irreds
  | otherwise = irreds `unionBags` listToBag extras

addIrred :: IrredKiCt -> InertKiIrreds -> InertKiIrreds
addIrred extra irreds = irreds `snocBag` extra

updIrreds :: (InertKiIrreds -> InertKiIrreds) -> InertKiCans -> InertKiCans
updIrreds upd ics = ics { inert_ki_irreds = upd (inert_ki_irreds ics) }

findMatchingIrreds :: InertKiIrreds -> CtKiEvidence -> (Bag (IrredKiCt, SwapFlag), InertKiIrreds)
findMatchingIrreds irreds ev 
  | KiCoPred _ lki1 rki1 <- classifyPredKind pred
  = partitionBagWith (match_kico lki1 rki1) irreds
  | otherwise
  = partitionBagWith match_non_kico irreds
  where
    pred = ctKiEvPred ev

    match_non_kico irred
      | irredCtPred irred `tcEqMonoKind` pred = Left (irred, NotSwapped)
      | otherwise = Right irred

    match_kico lki1 rki1 irred
      | KiCoPred _ lki2 rki2 <- classifyPredKind (irredCtPred irred)
      , Just swap <- match_kico_help lki1 rki1 lki2 rki2
      = Left (irred, swap)
      | otherwise
      = Right irred

    match_kico_help lki1 rki1 lki2 rki2
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

updGivenKiCos :: TcLevel -> KiCt -> InertKiCans -> InertKiCans
updGivenKiCos tclvl ct inerts@(IKC { inert_given_kico_lvl = kc_lvl })
  | not (isGivenCt ct) = inerts
  | not_kico ct = inerts
  | otherwise = inerts { inert_given_kico_lvl = kc_lvl'
                       , inert_given_kicos = True }
  where
    kc_lvl' | mentionsOuterVar tclvl (ctKiEvidence ct)
            = tclvl
            | otherwise
            = kc_lvl

    not_kico (CKiCoCan (KiCoCt { kc_lhs = KiVarLHS kv })) = not (isOuterKiVar tclvl kv)
    not_kico (CKiCoCan _) = panic "updGivenEqs"
    not_kico _ = False

data KiKickOutSpec
  = KOAfterUnify (MkVarSet TcKiVar)
  | KOAfterAdding CanKiCoLHS

kickOutRewritableLHSKi :: KiKickOutSpec -> CtFlavor -> InertKiCans -> (KiCts, InertKiCans)
kickOutRewritableLHSKi ko_spec new_f ics@(IKC { inert_kicos = kv_kicos
                                             , inert_ki_irreds = irreds })
  = (kicked_out, inert_cans_in)
  where
    inert_cans_in = ics { inert_kicos = kv_kicos_in
                        , inert_ki_irreds = irs_in }

    kicked_out :: KiCts
    kicked_out = (fmap CIrredCanKi irs_out)
                 `extendCtsList` fmap CKiCoCan kv_kicos_out

    (kv_kicos_out, kv_kicos_in) = partitionInertKiCos kick_out_kico kv_kicos
    (irs_out, irs_in) = partitionBag (kick_out_ct . CIrredCanKi) irreds

    f_kv_can_rewrite_ki :: (TcKiVar -> Bool) -> AnyMonoKind -> Bool
    f_kv_can_rewrite_ki = anyRewritableKiVar 

    {-# INLINE f_can_rewrite_ki #-}
    f_can_rewrite_ki :: AnyMonoKind -> Bool
    f_can_rewrite_ki = case ko_spec of
      KOAfterUnify kvs -> f_kv_can_rewrite_ki (`elemVarSet` kvs)
      KOAfterAdding (KiVarLHS kv) -> f_kv_can_rewrite_ki ((== kv) . toAnyKiVar)

    f_may_rewrite f = new_f `eqCanRewriteF` f

    kick_out_ct ct = f_may_rewrite (ctFlavor ct) && f_can_rewrite_ki (ctKiPred ct)

    kick_out_kico (KiCoCt { kc_lhs = lhs, kc_rhs = rhs_ki, kc_ev = ev })
      | not (f_may_rewrite f)
      = False
      | KiVarLHS _ <- lhs
      , f `eqCanRewriteF` new_f
      = False
      | f_can_rewrite_ki (canKiCoLHSKind lhs)
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
      KOAfterAdding lhs -> (`eqMonoKind` canKiCoLHSKind lhs)

    is_kivar_ki_for vs ki = case getKiVar_maybe ki of
                              Just kv
                                | Just tckv <- toTcKiVar_maybe kv
                                  -> tckv `elemVarSet` vs
                              _ -> False

{- *********************************************************************
*                                                                      *
                 Queries
*                                                                      *
********************************************************************* -}

mentionsOuterVar :: TcLevel -> CtKiEvidence -> Bool
mentionsOuterVar tclvl ev = anyFreeVarsOfMonoKind (isOuterKiVar tclvl) $ ctKiEvPred ev

isOuterKiVar :: TcLevel -> AnyKiVar -> Bool
isOuterKiVar tclvl kv
 = assertPpr (not (handleAnyKv (const False) (isTouchableMetaVar tclvl) kv))
   (ppr kv <+> ppr tclvl)
   $ tclvl `strictlyDeeperThan` (handleAnyKv (const topTcLevel) varLevel kv)

mightEqualLater
  :: InertKiSet -> AnyPredKind -> CtLoc -> AnyPredKind -> CtLoc -> Maybe (KvSubst AnyKiVar)
mightEqualLater inert_set given_pred given_loc wanted_pred wanted_loc
  = case tcUnifyKisFG bind_fun [given_pred] [wanted_pred] of
      Unifiable subst -> pprTrace "mightEqualLater 1" (ppr subst) $ Just subst
      MaybeApart reason subst
        | MARInfinite <- reason
        -> Nothing
        | otherwise
        -> pprTrace "mightEqualLater 2" (ppr subst) $ Just subst
      SurelyApart -> Nothing

  where
    in_scope = mkInScopeSet $ varsOfMonoKinds [given_pred, wanted_pred]

    bind_fun :: BindFun
    bind_fun kv rhs_ki
      | Just kv' <- toTcKiVar_maybe kv
      , isMetaVar kv'
      , can_unify kv' (metaVarInfo kv') rhs_ki
      = BindMe
      | otherwise
      = Apart

    can_unify :: TcKiVar -> MetaInfo -> AnyMonoKind -> Bool
    can_unify _ VarVar rhs_ki
      | Just rhs_kv <- getKiVar_maybe rhs_ki
      = handleAnyKv (const True) (\rhs_kv -> case tcVarDetails rhs_kv of
                                     MetaVar { mv_info = VarVar } -> True
                                     MetaVar {} -> False
                                     SkolemVar {} -> True ) rhs_kv
      | otherwise
      = False
    can_unify _ _ _ = False

{- *********************************************************************
*                                                                      *
    Cycle breakers
*                                                                      *
********************************************************************* -}

-- pushCycleBreakerVarStack :: CycleBreakerVarStack -> CycleBreakerVarStack
-- pushCycleBreakerVarStack = (emptyBag <|)

-- forAllCycleBreakerBindings_
--   :: Monad m => CycleBreakerVarStack -> (AnyTyVar AnyKiVar -> AnyType -> m ()) -> m ()
-- forAllCycleBreakerBindings_ (top_env :| _) action
--   = forM_ top_env (uncurry action)
-- {-# INLINABLE forAllCycleBreakerBindings_ #-}

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

solveOneFromTheOther :: KiCt -> KiCt -> InteractResult
solveOneFromTheOther ct_i ct_w
  | CtKiWanted {} <- ev_w
  = case ev_i of
      CtKiGiven {} -> KeepInert
      CtKiWanted {}
        | ((<) `on` ctLocSpan) loc_i loc_w -> KeepInert
        | otherwise -> KeepWork
  | CtKiWanted {} <- ev_i
  = KeepWork
  | lvl_i `sameDepthAs` lvl_w
  = same_level_strategy
  | otherwise
  = different_level_strategy

  where
    ev_i = ctKiEvidence ct_i
    ev_w = ctKiEvidence ct_w

    pred = ctKiEvPred ev_i

    loc_i = ctEvLoc ev_i
    loc_w = ctEvLoc ev_w
    orig_i = ctLocOrigin loc_i
    orig_w = ctLocOrigin loc_w
    lvl_i = ctLocLevel loc_i
    lvl_w = ctLocLevel loc_w

    different_level_strategy = if lvl_w `strictlyDeeperThan` lvl_i then KeepInert else KeepWork

    same_level_strategy = case (orig_i, orig_w) of
      _ -> KeepInert
      
