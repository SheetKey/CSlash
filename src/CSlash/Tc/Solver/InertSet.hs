{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module CSlash.Tc.Solver.InertSet where

import CSlash.Cs.Pass

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
import CSlash.Core.Type
import CSlash.Core.Type.FVs
import CSlash.Core.Type.Compare
import CSlash.Core.Kind.FVs
import CSlash.Core.Kind
import CSlash.Core.Subst
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

extendWorkListTyEqs :: TyRewriterSet -> Bag TyCt -> WorkList -> WorkList
extendWorkListTyEqs rewriters new_eqs wl
  | isEmptyTyRewriterSet rewriters
  = wl { wl_tyeqs = foldr (:) (wl_tyeqs wl) new_eqs }
  | otherwise
  = wl { wl_rw_tyeqs = foldr (:) (wl_rw_tyeqs wl) new_eqs }

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

extendWorkListTyImplic :: TyImplication -> WorkList -> WorkList
extendWorkListTyImplic implic wl = wl { wl_ty_implics = implic `consBag` wl_ty_implics wl }

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

type CycleBreakerVarStack = NonEmpty (Bag (TyVar Tc, Type Tc))

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

type InertKiCos = DVarEnv (KiVar Tc) KiCoCtList
type InertKiIrreds = Bag IrredKiCt

type InertTyEqs = DVarEnv (TyVar Tc) TyEqCtList
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

addTyEqToCans :: TcLevel -> TyEqCt -> InertTyCans -> InertTyCans
addTyEqToCans tc_lvl tyeq_ct@(TyEqCt { teq_lhs = lhs }) ics@(ITC { inert_tyeqs = eqs })
  = updGivenTyEqs tc_lvl (CTyEqCan tyeq_ct)
    $ case lhs of
        TyVarLHS tv -> ics { inert_tyeqs = addTyEq eqs tv tyeq_ct }

addTyEq :: InertTyEqs -> TyVar Tc -> TyEqCt -> InertTyEqs
addTyEq old_eqs tv ct
  = extendDVarEnv_C add_eq old_eqs tv [ct]
  where
    add_eq old_eqs _ = addToTyEqCtList ct old_eqs

addKiCoToCans :: TcLevel -> KiCoCt -> InertKiCans -> InertKiCans
addKiCoToCans tc_lvl kico_ct@(KiCoCt { kc_lhs = lhs }) ics@(IKC { inert_kicos = kicos })
  = updGivenKiCos tc_lvl (CKiCoCan kico_ct)
    $ case lhs of
        KiVarLHS kv -> ics { inert_kicos = addKiCo kicos kv kico_ct }

addKiCo :: InertKiCos -> KiVar Tc -> KiCoCt -> InertKiCos
addKiCo old_kicos v ct
  = extendDVarEnv_C add_kico old_kicos v [ct]
  where
    add_kico old_kicos _ = addToKiCoCtList ct old_kicos

foldKiCos :: (KiCoCt -> b -> b) -> InertKiCos -> b -> b
foldKiCos k kicos z = foldDVarEnv (\cts z -> foldr k z cts) z kicos

foldTyEqs :: (TyEqCt -> b -> b) -> InertTyEqs -> b -> b
foldTyEqs k eqs z = foldDVarEnv (\cts z -> foldr k z cts) z eqs

findTyEqs :: InertTyCans -> TyVar Tc -> [TyEqCt]
findTyEqs icans tv = concat @Maybe (lookupDVarEnv (inert_tyeqs icans) tv)

findTyEq :: InertTyCans -> CanTyEqLHS -> [TyEqCt]
findTyEq icans (TyVarLHS tv) = findTyEqs icans tv

findKiCos :: InertKiCans -> KiVar Tc -> [KiCoCt]
findKiCos icans kv = concat @Maybe (lookupDVarEnv (inert_kicos icans) kv)

findKiCo :: InertKiCans -> CanKiCoLHS -> [KiCoCt]
findKiCo icans (KiVarLHS kv) = findKiCos icans kv

{-# INLINE partition_tyeqs_container #-}
partition_tyeqs_container
  :: forall container
   . container
  -> (forall b. (TyEqCt -> b -> b) -> container -> b -> b)
  -> (TyEqCt -> container -> container)
  -> (TyEqCt -> Bool)
  -> container
  -> ([TyEqCt], container)
partition_tyeqs_container empty_container fold_container extend_container pred orig_inerts
  = fold_container folder orig_inerts ([], empty_container)
  where
    folder :: TyEqCt -> ([TyEqCt], container) -> ([TyEqCt], container)
    folder eq_ct (acc_true, acc_false)
      | pred eq_ct = (eq_ct : acc_true, acc_false)
      | otherwise = (acc_true, extend_container eq_ct acc_false)

partitionInertTyEqs
  :: (TyEqCt -> Bool)
  -> InertTyEqs
  -> ([TyEqCt], InertTyEqs)
partitionInertTyEqs = partition_tyeqs_container emptyTyEqs foldTyEqs addInertTyEqs

addInertTyEqs :: TyEqCt -> InertTyEqs -> InertTyEqs
addInertTyEqs eq_ct@(TyEqCt { teq_lhs = TyVarLHS tv }) eqs = addTyEq eqs tv eq_ct

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

addIrredTyToCans :: TcLevel -> IrredTyCt -> InertTyCans -> InertTyCans
addIrredTyToCans tc_lvl irred ics
  = updGivenTyEqs tc_lvl (CIrredCanTy irred)
    $ updIrredTys (addIrredTy irred) ics

addIrredKiToCans :: TcLevel -> IrredKiCt -> InertKiCans -> InertKiCans
addIrredKiToCans tc_lvl irred ics
  = updGivenKiCos tc_lvl (CIrredCanKi irred)
    $ updIrredKis (addIrredKi irred) ics

addIrredTys :: [IrredTyCt] -> InertTyIrreds -> InertTyIrreds
addIrredTys extras irreds
  | null extras = irreds
  | otherwise = irreds `unionBags` listToBag extras

addIrredKis :: [IrredKiCt] -> InertKiIrreds -> InertKiIrreds
addIrredKis extras irreds
  | null extras = irreds
  | otherwise = irreds `unionBags` listToBag extras

addIrredTy :: IrredTyCt -> InertTyIrreds -> InertTyIrreds
addIrredTy extra irreds = irreds `snocBag` extra

addIrredKi :: IrredKiCt -> InertKiIrreds -> InertKiIrreds
addIrredKi extra irreds = irreds `snocBag` extra

updIrredTys :: (InertTyIrreds -> InertTyIrreds) -> InertTyCans -> InertTyCans
updIrredTys upd ics = ics { inert_ty_irreds = upd (inert_ty_irreds ics) }

updIrredKis :: (InertKiIrreds -> InertKiIrreds) -> InertKiCans -> InertKiCans
updIrredKis upd ics = ics { inert_ki_irreds = upd (inert_ki_irreds ics) }

findMatchingIrredTys
  :: InertTyIrreds -> CtTyEvidence -> (Bag (IrredTyCt, SwapFlag), InertTyIrreds)
findMatchingIrredTys irreds ev
  | TyEqPred lty1 rty1 <- classifyPredType pred
  = partitionBagWith (match_eq lty1 rty1) irreds
  | otherwise
  = partitionBagWith match_non_eq irreds
  where
    pred = ctTyEvPred ev

    match_non_eq irred
      | irredTyCtPred irred `tcEqType` pred = Left (irred, NotSwapped)
      | otherwise = Right irred

    match_eq lty1 rty1 irred
      | TyEqPred lty2 rty2 <- classifyPredType (irredTyCtPred irred)
      , Just swap <- match_eq_help lty1 rty1 lty2 rty2
      = Left (irred, swap)
      | otherwise
      = Right irred

    match_eq_help lty1 rty1 lty2 rty2
      | lty1 `tcEqType` lty2, rty1 `tcEqType` rty2
      = Just NotSwapped
      | lty1 `tcEqType` rty2, rty1 `tcEqType` lty2
      = Just IsSwapped
      | otherwise
      = Nothing

findMatchingIrredKis
  :: InertKiIrreds -> CtKiEvidence -> (Bag (IrredKiCt, SwapFlag), InertKiIrreds)
findMatchingIrredKis irreds ev 
  | KiCoPred _ lki1 rki1 <- classifyPredKind pred
  = partitionBagWith (match_kico lki1 rki1) irreds
  | otherwise
  = partitionBagWith match_non_kico irreds
  where
    pred = ctKiEvPred ev

    match_non_kico irred
      | irredKiCtPred irred `tcEqMonoKind` pred = Left (irred, NotSwapped)
      | otherwise = Right irred

    match_kico lki1 rki1 irred
      | KiCoPred _ lki2 rki2 <- classifyPredKind (irredKiCtPred irred)
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

-- Need to handle [Let-bound skolems] if I ever add `t1 ~ t2` in user code
updGivenTyEqs :: TcLevel -> TyCt -> InertTyCans -> InertTyCans
updGivenTyEqs tclvl ct inerts
  | not (isGivenCt ct) = inerts
  | otherwise = inerts { inert_given_tyeq_lvl = tclvl
                       , inert_given_tyeqs = True }

updGivenKiCos :: TcLevel -> KiCt -> InertKiCans -> InertKiCans
updGivenKiCos tclvl ct inerts@(IKC { inert_given_kico_lvl = kc_lvl })
  | not (isGivenCt ct) = inerts
  | otherwise = inerts { inert_given_kico_lvl = tclvl
                       , inert_given_kicos = True }

data KiKickOutSpec
  = KOAfterUnify (VarSet TcKiVar)
  | KOAfterAdding CanKiCoLHS

data TyKickOutSpec
  = TKOAfterUnify (VarSet TcTyVar)
  | TKOAfterAdding CanTyEqLHS

kickOutRewritableLHSTy :: TyKickOutSpec -> CtFlavor -> InertTyCans -> (TyCts, InertTyCans)
kickOutRewritableLHSTy ko_spec new_f ics@(ITC { inert_tyeqs = tv_eqs
                                              , inert_ty_irreds = irreds })
  = (kicked_out, inert_cans_in)
  where
    inert_cans_in = ics { inert_tyeqs = tv_eqs_in
                        , inert_ty_irreds = irs_in }

    kicked_out :: TyCts
    kicked_out = (fmap CIrredCanTy irs_out)
                 `extendCtsList` fmap CTyEqCan tv_eqs_out

    (tv_eqs_out, tv_eqs_in) = partitionInertTyEqs kick_out_eq tv_eqs
    (irs_out, irs_in) = partitionBag kick_out_irred irreds

    
    f_tv_can_rewrite_ty :: Bool -> (TyVar Tc -> Bool) -> Type Tc -> Bool
    f_tv_can_rewrite_ty look check_tv ty = anyRewritableTyVar can_rewrite ty
      where
        can_rewrite tv = look && check_tv tv

    f_can_rewrite_ty :: Bool -> Type Tc -> Bool
    f_can_rewrite_ty look = case ko_spec of
      TKOAfterUnify tvs -> f_tv_can_rewrite_ty look (\tv -> case toTcTyVar_maybe tv of
                                                              Just tv -> tv `elemVarSet` tvs
                                                              Nothing -> False)
      TKOAfterAdding (TyVarLHS tv) -> f_tv_can_rewrite_ty look (== tv)

    f_may_rewrite f = new_f `eqCanRewriteF` f

    kick_out_irred (IrredTyCt { itr_ev = ev })
      = f_may_rewrite (ctEvFlavor ev)
        && f_can_rewrite_ty True pred
      where
        pred = ctTyEvPred ev

    kick_out_eq (TyEqCt { teq_lhs = lhs, teq_rhs = rhs_ty, teq_ev = ev })
      | not (f_may_rewrite f)
      = False
      | f_can_rewrite_ty True (canTyEqLHSType lhs)
      = True
      | let look | f_can_rewrite_f = False
                 | otherwise = True
      , f_can_rewrite_ty look rhs_ty
      = True
      | not f_can_rewrite_f
      , is_new_lhs rhs_ty
      = True
      | otherwise = False
      where
        f_can_rewrite_f = f `eqCanRewriteF` new_f
        f = ctEvFlavor ev

    is_new_lhs = case ko_spec of
      TKOAfterUnify tvs -> is_tyvar_ty_for tvs
      TKOAfterAdding lhs -> (`eqType` canTyEqLHSType lhs)

    is_tyvar_ty_for tvs ty = case getTyVar_maybe ty of
                               Just tv
                                 | Just tctv <- toTcTyVar_maybe tv
                                   -> tctv `elemVarSet` tvs
                               _ -> False
      
-- TODO: REWRITE THIS
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
    (irs_out, irs_in) = partitionBag kick_out_irred irreds

    f_kv_can_rewrite_ki :: Bool -> (KiVar Tc -> Bool) -> MonoKind Tc -> Bool
    f_kv_can_rewrite_ki look check_kv ki
      = anyRewritableKiVar can_rewrite ki
      where
        can_rewrite kv = look && check_kv kv

    f_can_rewrite_ki :: Bool -> MonoKind Tc -> Bool
    f_can_rewrite_ki look = case ko_spec of
      KOAfterUnify kvs -> f_kv_can_rewrite_ki look (\kv -> case toTcKiVar_maybe kv of
                                                             Just kv -> kv `elemVarSet` kvs
                                                             Nothing -> False)
      KOAfterAdding (KiVarLHS kv) -> f_kv_can_rewrite_ki look (== kv)

    f_may_rewrite f = new_f `eqCanRewriteF` f

    kick_out_irred (IrredKiCt { ikr_ev = ev })
      = f_may_rewrite (ctEvFlavor ev) && f_can_rewrite_ki True (ctKiEvPred ev)

    kick_out_kico (KiCoCt { kc_lhs = lhs, kc_rhs = rhs_ki, kc_ev = ev })
      | not (f_may_rewrite f)
      = False
      | f_can_rewrite_ki True (canKiCoLHSKind lhs)
      = True
      | let look | f_can_rewrite_f = False
                 | otherwise = True
      , f_can_rewrite_ki look rhs_ki
      = True
      | not f_can_rewrite_f
      , is_new_lhs_ki rhs_ki
      = True
      | otherwise = False
      where
        f_can_rewrite_f = f `eqCanRewriteF` new_f
        f = ctEvFlavor ev

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
mentionsOuterVar tclvl ev = anyFreeVarsOfMonoKind (isOuterVar tclvl) $ ctKiEvPred ev

isOuterVar :: TcVar v => TcLevel -> v -> Bool
isOuterVar tclvl v
 = assertPpr (not (isTouchableMetaVar tclvl v))
   (ppr v <+> ppr tclvl)
   $ tclvl `strictlyDeeperThan` (varLevel v)

mightEqualLater
  :: InertKiSet -> PredKind Tc -> CtLoc -> PredKind Tc -> CtLoc -> Maybe (Subst Tc Tc)
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

    can_unify :: TcKiVar -> MetaInfo -> MonoKind Tc -> Bool
    can_unify _ VarVar rhs_ki
      | Just rhs_kv <- getKiVar_maybe rhs_ki
      = case tcVarDetails rhs_kv of
          MetaVar { mv_info = VarVar } -> True
          MetaVar {} -> False
          SkolemVar {} -> True
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

solveOneTyFromTheOther :: TyCt -> TyCt -> InteractResult
solveOneTyFromTheOther ct_i ct_w
  | CtTyWanted {} <- ev_w
  = case ev_i of
      CtTyGiven {} -> KeepInert
      CtTyWanted {}
        | ((<) `on` ctLocSpan) loc_i loc_w -> KeepInert
        | otherwise -> KeepWork
  | CtTyWanted {} <- ev_i
  = KeepWork
  | lvl_i `sameDepthAs` lvl_w
  = same_level_strategy
  | otherwise
  = different_level_strategy
  where
    ev_i = ctTyEvidence ct_i
    ev_w = ctTyEvidence ct_w

    loc_i = ctEvLoc ev_i
    loc_w = ctEvLoc ev_w
    orig_i = ctLocOrigin loc_i
    orig_w = ctLocOrigin loc_w
    lvl_i = ctLocLevel loc_i
    lvl_w = ctLocLevel loc_w

    different_level_strategy = if lvl_w `strictlyDeeperThan` lvl_i then KeepInert else KeepWork

    same_level_strategy = case (orig_i, orig_w) of
      _ -> KeepInert
  
solveOneKiFromTheOther :: KiCt -> KiCt -> InteractResult
solveOneKiFromTheOther ct_i ct_w
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

    loc_i = ctEvLoc ev_i
    loc_w = ctEvLoc ev_w
    orig_i = ctLocOrigin loc_i
    orig_w = ctLocOrigin loc_w
    lvl_i = ctLocLevel loc_i
    lvl_w = ctLocLevel loc_w

    different_level_strategy = if lvl_w `strictlyDeeperThan` lvl_i then KeepInert else KeepWork

    same_level_strategy = case (orig_i, orig_w) of
      _ -> KeepInert
      
