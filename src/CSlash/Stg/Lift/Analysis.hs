module CSlash.Stg.Lift.Analysis
  ( Skeleton(..), BinderInfo(..), binderInfoBndr
  , LlStgBinding, LlStgExpr, LlStgRhs, LlStgAlt, tagSkeletonTopBind

  , goodToLift
  -- , closureGrowth
  ) where

import CSlash.Platform
import CSlash.Platform.Profile

import CSlash.Core

import CSlash.Types.Basic
import CSlash.Types.Demand
import CSlash.Types.Var.Id

-- import GHC.Runtime.Heap.Layout ( WordOff )

import CSlash.Stg.Lift.Config
import CSlash.Stg.Lift.Types
import CSlash.Stg.Syntax

-- import qualified GHC.StgToCmm.ArgRep  as StgToCmm.ArgRep
-- import qualified GHC.StgToCmm.Closure as StgToCmm.Closure
-- import qualified GHC.StgToCmm.Layout  as StgToCmm.Layout
import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Types.Var.Set

import CSlash.Utils.Panic

import Data.Maybe ( mapMaybe )

llTrace :: String -> SDoc -> a -> a
llTrace _ _ c = c

mkArgOccs :: [StgArg] -> CoreIdSet
mkArgOccs = mkVarSet . mapMaybe stg_arg_var
  where
    stg_arg_var (StgVarArg occ) = Just occ
    stg_arg_var _ = Nothing

tagSkeletonTopBind :: CgStgBinding -> LlStgBinding
tagSkeletonTopBind bind = bind'
  where
    (_, _, _, bind') = tagSkeletonBinding False NilSk emptyVarSet bind

tagSkeletonExpr :: CgStgExpr -> (Skeleton, CoreIdSet, LlStgExpr)
tagSkeletonExpr (StgLit lit) = (NilSk, emptyVarSet, StgLit lit)
tagSkeletonExpr (StgConApp con mn args) = (NilSk, mkArgOccs args, StgConApp con mn args)
tagSkeletonExpr (StgApp f args) = (NilSk, arg_occs, StgApp f args)
  where arg_occs | null args = unitVarSet f
                 | otherwise = mkArgOccs args
tagSkeletonExpr (StgCase scrut bndr ty alts)
  = (skel, arg_occs, StgCase scrut' bndr' ty alts')
  where
    (scrut_skel, scrut_arg_occs, scrut') = tagSkeletonExpr scrut
    (alt_skels, alt_arg_occss, alts') = mapAndUnzip3 tagSkeletonAlt alts
    skel = bothSk scrut_skel (foldr altSk NilSk alt_skels)
    arg_occs = unionVarSets (scrut_arg_occs:alt_arg_occss) `delVarSet` bndr
    bndr' = BoringBinder bndr
tagSkeletonExpr (StgTick t e)
  = (skel, arg_occs, StgTick t e')
  where (skel, arg_occs, e') = tagSkeletonExpr e
tagSkeletonExpr (StgLet _ bind body) = tagSkeletonLet False body bind
tagSkeletonExpr (StgLetNoEscape _ bind body) = tagSkeletonLet True body bind

mkLet :: Bool -> Skeleton -> LlStgBinding -> LlStgExpr -> LlStgExpr
mkLet True = StgLetNoEscape
mkLet _ = StgLet

tagSkeletonLet :: Bool -> CgStgExpr -> CgStgBinding -> (Skeleton, CoreIdSet, LlStgExpr)
tagSkeletonLet is_lne body bind
  = (let_skel, arg_occs, mkLet is_lne scope bind' body')
  where
    (body_skel, body_arg_occs, body') = tagSkeletonExpr body
    (let_skel, arg_occs, scope, bind')
      = tagSkeletonBinding is_lne body_skel body_arg_occs bind

tagSkeletonBinding
  :: Bool
  -> Skeleton
  -> CoreIdSet
  -> CgStgBinding
  -> (Skeleton, CoreIdSet, Skeleton, LlStgBinding)
tagSkeletonBinding is_lne body_skel body_arg_occs (StgNonRec bndr rhs)
  = (let_skel, arg_occs, scope, bind')
  where
    (rhs_skel, rhs_arg_occs, rhs') = tagSkeletonRhs bndr rhs
    arg_occs = (body_arg_occs `unionVarSet` rhs_arg_occs) `delVarSet` bndr
    bind_skel
      | is_lne = rhs_skel
      | otherwise = ClosureSk bndr (freeVarsOfRhs rhs) rhs_skel
    let_skel = bothSk body_skel bind_skel
    occurs_as_arg = bndr `elemVarSet` body_arg_occs
    scope = body_skel
    bind' = StgNonRec (BindsClosure bndr occurs_as_arg) rhs'

tagSkeletonBinding is_lne body_skel body_arg_occs (StgRec pairs)
  = (let_skel, arg_occs, scope, StgRec pairs')
  where
    (bndrs, _) = unzip pairs

    skel_occs_rhss' = map (uncurry tagSkeletonRhs) pairs
    rhss_arg_occs = map sndOf3 skel_occs_rhss'
    scope_occs = unionVarSets (body_arg_occs : rhss_arg_occs)
    arg_occs = scope_occs `delVarSetList` bndrs

    scope = foldr (bothSk . fstOf3) body_skel skel_occs_rhss'

    (bind_skels, pairs') = unzip (zipWith single_bind bndrs skel_occs_rhss')
    let_skel = foldr bothSk body_skel bind_skels

    single_bind bndr (skel_rhs, _, rhs') = (bind_skel, (bndr', rhs'))
      where
        bind_skel | is_lne = skel_rhs
                  | otherwise = ClosureSk bndr fvs skel_rhs
        fvs = freeVarsOfRhs rhs' `dVarSetMinusVarSet` mkVarSet bndrs
        bndr' = BindsClosure bndr (bndr `elemVarSet` scope_occs)

tagSkeletonRhs :: CoreId -> CgStgRhs -> (Skeleton, CoreIdSet, LlStgRhs)
tagSkeletonRhs _ (StgRhsCon dc mn ts args ty)
  = (NilSk, mkArgOccs args, StgRhsCon dc mn ts args ty)
tagSkeletonRhs bndr (StgRhsClosure fvs bndrs body ty)
  = (rhs_skel, body_arg_occs, StgRhsClosure fvs bndrs' body' ty)
  where
    bndrs' = map BoringBinder bndrs
    (body_skel, body_arg_occs, body') = tagSkeletonExpr body
    rhs_skel = rhsSk (rhsCard bndr) body_skel

rhsCard :: CoreId -> Card
rhsCard bndr
  | idArity bndr == 0 = oneifyCard n
  | otherwise = n `multCard` (sndOf3 $ peelManyCalls (idArity bndr) cd)
  where
    n :* cd = idDemandInfo bndr

tagSkeletonAlt :: CgStgAlt -> (Skeleton, CoreIdSet, LlStgAlt)
tagSkeletonAlt old@GenStgAlt{ alt_bndrs = bndrs, alt_rhs = rhs }
  = (alt_skel, arg_occs, old { alt_bndrs = fmap BoringBinder bndrs, alt_rhs = rhs' })
  where
    (alt_skel, alt_arg_occs, rhs') = tagSkeletonExpr rhs
    arg_occs = alt_arg_occs `delVarSetList` bndrs

goodToLift
  :: StgLiftConfig
  -> TopLevelFlag
  -> RecFlag
  -> (DCoreIdSet -> DCoreIdSet)
  -> [(BinderInfo, LlStgRhs)]
  -> Skeleton
  -> Maybe DCoreIdSet
goodToLift cfg top_lvl rec_flag expander pairs scope = decide
  [ ("top-level", isTopLevel top_lvl)
  , ("memoized", any_memoized)
  , ("argument occurrences", arg_occs)
  , ("join point", is_join_point)
  , ("abstracts known local function", abstracts_known_local_fun)
  -- , ("args spill on stack", args_spill_on_stack)
  , ("increases allocation", inc_allocs)
  ]
  where
    profile = c_targetProfile cfg
    platform = profilePlatform profile
    decide deciders
      | not (my_or deciders)
      = llTrace "stgLiftLams:lifting"
        (ppr bndrs <+> ppr abs_ids $$ ppr allocs $$ ppr scope) $
        Just abs_ids
      | otherwise
      = Nothing
    ppr_deciders = vcat . map (text . fst) . filter snd
    my_or deciders
      = llTrace "stgLiftLams:goodToLift" (ppr bndrs $$ ppr_deciders deciders) $
        any snd deciders

    bndrs = map (binderInfoBndr . fst) pairs
    bndrs_set = mkVarSet bndrs
    rhss = map snd pairs

    fvs = unionDVarSets (map freeVarsOfRhs rhss)

    abs_ids = expander (delDVarSetList fvs bndrs)

    any_memoized = any is_memoized_rhs rhss
    is_memoized_rhs StgRhsCon{} = True
    is_memoized_rhs (StgRhsClosure _ _ _ _) = False

    arg_occs = or (mapMaybe (binderInfoOccursAsArg . fst) pairs)

    is_join_point = any isJoinId bndrs

    abstracts_join_ids = any isJoinId (dVarSetElems abs_ids)

    known_fun id = idArity id > 0
    abstracts_known_local_fun
      = not (c_liftLamsKnown cfg) && any known_fun (dVarSetElems abs_ids)

    inc_allocs = panic "inc_allocs"
    allocs = ()
