module CSlash.Core.Opt.Simplify.Inline where

import CSlash.Driver.Flags

import CSlash.Core.Opt.Simplify.Env

import CSlash.Core
import CSlash.Core.Unfold
import CSlash.Core.FVs( exprFreeIds )

import CSlash.Types.Var.Id
import CSlash.Types.Var.Env( InScopeSet, lookupInScope )
import CSlash.Types.Var.Set
import CSlash.Types.Basic  ( Arity, RecFlag(..), isActive )
import CSlash.Utils.Logger
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Types.Name

import Data.List (isPrefixOf)

{- *********************************************************************
*                                                                      *
               considerUnfolding
*                                                                      *
********************************************************************* -}

couldBeSmallEnoughToInline :: UnfoldingOpts -> Int -> CoreExpr -> Bool
couldBeSmallEnoughToInline opts threshold rhs
  = case sizeExpr opts threshold [] body of
      TooBig -> False
      _ -> True
  where
    (_, body) = collectBinders rhs

smallEnoughToInline :: UnfoldingOpts -> Unfolding -> Bool
smallEnoughToInline opts CoreUnfolding{ uf_guidance = guidance }
  = case guidance of
      UnfIfGoodArgs{ ug_size = size } -> size <= unfoldingUseThreshold opts
      UnfWhen{} -> True
      UnfNever -> False
smallEnoughToInline _ _ = False

{- *********************************************************************
*                                                                      *
               callSiteInline
*                                                                      *
********************************************************************* -}

callSiteInline
  :: SimplEnv
  -> Logger
  -> CoreId
  -> Bool
  -> [ArgSummary]
  -> CallCtxt
  -> Maybe CoreExpr
callSiteInline env logger id lone_variable arg_infos cont_info
  = case idUnfolding id of
      CoreUnfolding { uf_tmpl = unf_template
                    , uf_cache = unf_cache
                    , uf_guidance = guidance }
        | active_unf -> tryUnfolding env logger id lone_variable
                        arg_infos cont_info unf_template unf_cache guidance
        | otherwise -> traceInline logger uf_opts id "Inactive unfolding:" (ppr id) Nothing

      NoUnfolding -> Nothing
      OtherCon{} -> Nothing
  where
    uf_opts = seUnfoldingOpts env
    active_unf = activeUnfolding (seMode env) id

activeUnfolding :: SimplMode -> CoreId -> Bool
activeUnfolding mode id
  | isCompulsoryUnfolding (realIdUnfolding id)
  = True
  | otherwise
  = isActive (sm_phase mode) (idInlineActivation id)
    && sm_inline mode

{-# INLINE traceInline #-}
traceInline :: Logger -> UnfoldingOpts -> CoreId -> String -> SDoc -> a -> a
traceInline logger opts inline_id str doc result
  | enable = logTraceMsg logger str doc result
  | otherwise = result
  where
    enable | logHasDumpFlag logger Opt_D_dump_verbose_inlinings
           = True
           | Just prefix <- unfoldingReportPrefix opts
           = prefix `isPrefixOf` occNameString (getOccName inline_id)
           | otherwise
           = False

tryUnfolding
  :: SimplEnv
  -> Logger
  -> CoreId
  -> Bool
  -> [ArgSummary]
  -> CallCtxt
  -> CoreExpr
  -> UnfoldingCache
  -> UnfoldingGuidance
  -> Maybe CoreExpr
tryUnfolding env logger id lone_variable arg_infos cont_info unf_template unf_cache guidance
  = case guidance of
      UnfNever -> traceInline logger opts id str (text "UnfNever") Nothing

      UnfWhen { ug_arity = uf_arity, ug_unsat_ok = unsat_ok, ug_boring_ok = boring_ok }
        | enough_args && (boring_ok || some_benefit || unfoldingVeryAggressive opts)
          -> traceInline logger opts id str (mk_doc some_benefit empty True)
             (Just unf_template)

        | otherwise
          -> traceInline logger opts id str (mk_doc some_benefit empty False) Nothing
        where
          some_benefit = calc_some_benefit uf_arity True
          enough_args = (n_val_args >= uf_arity) || (unsat_ok && n_val_args > 0)

      UnfIfGoodArgs { ug_args = arg_discounts, ug_res = res_discount, ug_size = size }
        | isJoinId id, small_enough -> inline_join_point
        | unfoldingVeryAggressive opts -> yes
        | is_wf, some_benefit, small_enough -> yes
        | otherwise -> no
        where
          yes = traceInline logger opts id str (mk_doc some_benefit extra_doc True)
                (Just unf_template)
          no = traceInline logger opts id str (mk_doc some_benefit extra_doc False) Nothing

          some_benefit = calc_some_benefit (length arg_discounts) False

          depth_threshold = unfoldingCaseThreshold opts
          depth_scaling = unfoldingCaseScaling opts
          depth_penalty | case_depth <= depth_threshold = 0
                        | otherwise = (size * (case_depth - depth_threshold))
                                      `div` depth_scaling

          adjusted_size = size + depth_penalty - discount
          small_enough = adjusted_size <= unfoldingUseThreshold opts
          discount = computeDiscount arg_discounts res_discount arg_infos cont_info

          extra_doc = vcat [ ppWhen (isJoinId id) $
                             text "join" <+> fsep [ ppr ( v
                                                        , hasCoreUnfolding (idUnfolding v)
                                                        , fmap (isEvaldUnfolding . idUnfolding)
                                                          (lookupInScope in_scope v)
                                                        , is_more_evald in_scope v )
                                                  | v <- vselems (exprFreeIds unf_template) ]
                           , text "depth based penalty =" <+> int depth_penalty
                           , text "adjusted size =" <+> int adjusted_size ]

          inline_join_point
            | or (zipWith scrut_arg arg_discounts arg_infos)
            = yes
            | anyVarSet (is_more_evald in_scope)
              $ exprFreeIds unf_template
            = yes
            | otherwise
            = no

          scrut_arg disc ValueArg = disc > 0
          scrut_arg _ _ = False

  where
    opts = seUnfoldingOpts env
    case_depth = seCaseDepth env
    inline_depth = seInlineDepth env
    in_scope = seIdInScope env 

    UnfoldingCache { uf_is_work_free = is_wf, uf_expandable = is_exp } = unf_cache

    mk_doc some_benefit extra_doc yes_or_no
      = vcat [ text "arg infos" <+> ppr arg_infos
             , text"interesting continuation" <+> ppr cont_info
             , text "some_benefit" <+> ppr some_benefit
             , text "is exp:" <+> ppr is_exp
             , text "is work-free:" <+> ppr is_wf
             , text "guidance" <+> ppr guidance
             , text "case depth =" <+> int case_depth
             , text "inline depth =" <+> int inline_depth
             , extra_doc
             , text "ANSWER =" <+> if yes_or_no then text "YES" else text "NO" ]

    ctx = log_default_dump_context (logFlags logger)
    str = "Considering inlining: " ++ showSDocOneLine ctx (ppr id)
    n_val_args = length arg_infos

    calc_some_benefit :: Arity -> Bool -> Bool
    calc_some_benefit uf_arity is_inline
      | not saturated = interesting_args
      | otherwise = interesting_args || interesting_call
      where
        saturated = n_val_args >= uf_arity
        over_saturated = n_val_args > uf_arity
        interesting_args = any nonTriv arg_infos

        interesting_call
          | over_saturated
          = True
          | otherwise
          = case cont_info of
              CaseCtxt -> not (lone_variable && is_exp)
              ValAppCtxt -> True
              RuleArgCtxt -> uf_arity > 0
              DiscArgCtxt -> uf_arity > 0
              RhsCtxt NonRecursive | is_inline -> uf_arity > 0
              _ -> False

vselems :: CoreIdSet -> [CoreId]
vselems s = nonDetStrictFoldVarSet (\v vs -> v : vs) [] s

is_more_evald :: InScopeSet CoreId -> CoreId -> Bool
is_more_evald in_scope v
  | Just v1 <- lookupInScope in_scope v
  , idUnfolding v1 `isBetterUnfoldingThan` idUnfolding v
  = True
  | otherwise
  = False

computeDiscount :: [Int] -> Int -> [ArgSummary] -> CallCtxt -> Int
computeDiscount arg_discounts res_discount arg_infos cont_info
  = 10
    + 10 * length actual_arg_discounts
    + total_arg_discount
    + res_discount'
  where
    actual_arg_discounts = zipWith mk_arg_discount arg_discounts arg_infos
    total_arg_discount = sum actual_arg_discounts

    mk_arg_discount _ TrivArg = 0
    mk_arg_discount _ NonTrivArg = 10
    mk_arg_discount discount ValueArg = discount

    res_discount'
      | LT <- arg_discounts `compareLength` arg_infos
      = res_discount
      | otherwise
      = case cont_info of
          BoringCtxt -> 0
          CaseCtxt -> res_discount
          ValAppCtxt -> res_discount
          _ -> 40 `min` res_discount
