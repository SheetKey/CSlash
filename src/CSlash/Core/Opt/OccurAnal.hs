{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -fmax-worker-args=122 #-}

module CSlash.Core.Opt.OccurAnal where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Core as Core
import CSlash.Core.FVs
import CSlash.Core.Utils   ( exprIsTrivial, {-isDefaultAlt,-} isExpandableApp,
                             mkCastMCo, mkTicks )
import CSlash.Core.Opt.Arity   ( joinRhsArity, isOneShotBndr )
-- import GHC.Core.Coercion
import CSlash.Core.Type
import CSlash.Core.Kind
-- import CSlash.Core.Type.FVs    ( tyCoVarsOfMCo )

import CSlash.Data.Maybe( orElse, mapMaybe )
import CSlash.Data.Graph.Directed ( SCC(..), Node(..)
                                  , stronglyConnCompFromEdgedVerticesUniq
                                  , stronglyConnCompFromEdgedVerticesUniqR )
import CSlash.Types.Unique
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.Set
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.Basic
import CSlash.Types.Tickish
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Types.Var
import CSlash.Types.Demand ( argOneShots, argsOneShots, isDeadEndSig )

import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc
import CSlash.Utils.Trace
import CSlash.Utils.Constants (debugIsOn)

-- import GHC.Builtin.Names( runRWKey )
import CSlash.Unit.Module( Module )

import Data.List (mapAccumL)
import Data.List.NonEmpty (NonEmpty (..))

occurAnalyzeExpr :: CoreExpr -> CoreExpr
occurAnalyzeExpr expr = expr'
  where WUD _ expr' = occAnal initOccEnv expr

occurAnalyzePgm
  :: Module
  -> (Id Zk -> Bool)
  -> CoreProgram
  -> CoreProgram
occurAnalyzePgm this_mod active_unf binds
  | isEmptyDetails final_usage
  = occ_anald_binds
  | otherwise
  = warnPprTrace True "Glomming in" (hang (ppr this_mod <> colon) 2 (ppr final_usage))
    (panic "occ_anald_glommed_binds Not possible")
  where
    init_env = initOccEnv { occ_unf_act = active_unf }

    WUD final_usage occ_anald_binds = go binds init_env

    go :: [CoreBind ] -> OccEnv -> WithUsageDetails [CoreBind]
    go [] _ = WUD emptyDetails []
    go (bind:binds) env = occAnalBind env TopLevel bind (go binds) (++)

{- *********************************************************************
*                                                                      *
                Bindings
*                                                                      *
********************************************************************* -}

occAnalBind
  :: OccEnv
  -> TopLevelFlag
  -> CoreBind
  -> (OccEnv -> WithUsageDetails r)
  -> ([CoreBind] -> r -> r)
  -> WithUsageDetails r
occAnalBind env lvl (Rec pairs) thing_inside combine
  = addInScopeList env (map fst pairs) $ \env ->
    let WUD body_uds body' = thing_inside env
        WUD bind_uds binds' = occAnalRecBind env lvl pairs body_uds
    in WUD bind_uds (combine binds' body')

occAnalBind !env lvl (NonRec bndr rhs) thing_inside combine
  | mb_join@(JoinPoint {}) <- idJoinPointHood bndr
  = let !(rhs_uds_s, bndr', rhs') = occAnalNonRecRhs env lvl mb_join bndr rhs
        rhs_uds = foldr1 orUDs rhs_uds_s
        !(WUD body_uds (occ, body)) = occAnalNonRecBody env bndr' $ \env ->
                                      thing_inside (addJoinPoint env bndr' rhs_uds)
    in if isDeadOcc occ
       then WUD body_uds body
       else WUD (rhs_uds `orUDs` body_uds)
                (combine [NonRec (fst (tagNonRecBinder lvl occ bndr')) rhs'] body)

  | WUD body_uds (occ, body) <- occAnalNonRecBody env bndr thing_inside
  = if isDeadOcc occ
    then WUD body_uds body
    else let (tagged_bndr, mb_join) = tagNonRecBinder lvl occ bndr
             !(rhs_uds_s, final_bndr, rhs') = occAnalNonRecRhs env lvl mb_join tagged_bndr rhs
         in WUD (foldr andUDs body_uds rhs_uds_s)
                (combine [NonRec final_bndr rhs'] body)

  | otherwise
  = panic "Impossible, all cases covered"

occAnalNonRecBody
  :: OccEnv
  -> CoreId
  -> (OccEnv -> WithUsageDetails r)
  -> (WithUsageDetails (OccInfo, r))
occAnalNonRecBody env bndr thing_inside
  = addInScopeOne env bndr $ \env ->
    let !(WUD inner_uds res) = thing_inside env
        !occ = lookupLetOccInfo inner_uds bndr
    in WUD inner_uds (occ, res)

occAnalNonRecRhs
  :: OccEnv
  -> TopLevelFlag
  -> JoinPointHood
  -> CoreId
  -> CoreExpr
  -> ([UsageDetails], CoreId, CoreExpr)
occAnalNonRecRhs !env lvl mb_join bndr rhs
  = ([adj_rhs_uds, adj_unf_uds], final_bndr, final_rhs)
  where
    -- RHS
    rhs_env = mkRhsOccEnv env NonRecursive rhs_ctxt mb_join bndr rhs
    rhs_ctxt = mkNonRecRhsCtxt lvl bndr unf

    WUD adj_rhs_uds final_rhs = adjustNonRecRhs mb_join $ occAnalLamTail rhs_env rhs
    final_bndr | noBinderSwaps env = bndr
               | otherwise = bndr `setIdUnfolding` unf1

    -- Unfolding
    unf = idUnfolding bndr
    WTUD unf_tuds unf1 = occAnalUnfolding rhs_env unf
    adj_unf_uds = adjustTailArity mb_join unf_tuds

mkNonRecRhsCtxt :: TopLevelFlag -> Id Zk -> Unfolding -> OccEncl
mkNonRecRhsCtxt lvl bndr unf
  | certainly_inline = OccVanilla
  | otherwise = OccRhs
  where
    certainly_inline = case idOccInfo bndr of
                         OneOcc { occ_in_lam = NotInsideLam, occ_n_br = 1 }
                           -> active && not stable_unf && not top_bottoming
                         _ -> False

    active = isAlwaysActive (idInlineActivation bndr)
    stable_unf = isStableUnfolding unf
    top_bottoming = isTopLevel lvl && isDeadEndId bndr

occAnalRecBind
  :: OccEnv
  -> TopLevelFlag
  -> [(CoreId, CoreExpr)]
  -> UsageDetails
  -> WithUsageDetails [CoreBind]
occAnalRecBind !rhs_env lvl pairs body_usage
  = foldr (occAnalRec rhs_env lvl) (WUD body_usage []) sccs
  where
    sccs = stronglyConnCompFromEdgedVerticesUniq nodes

    nodes = map (makeNode rhs_env bndr_set) pairs

    bndrs = map fst pairs
    bndr_set = mkVarSet bndrs

occAnalRec
  :: OccEnv
  -> TopLevelFlag
  -> SCC NodeDetails
  -> WithUsageDetails [CoreBind]
  -> WithUsageDetails [CoreBind]
occAnalRec !_ lvl (AcyclicSCC (ND { nd_bndr = bndr, nd_rhs = wtuds })) (WUD body_uds binds)
  | isDeadOcc occ
  = WUD body_uds binds
  | otherwise
  = let (bndr', mb_join) = tagNonRecBinder lvl occ bndr
        !(WUD rhs_uds' rhs') = adjustNonRecRhs mb_join wtuds
    in WUD (body_uds `andUDs` rhs_uds') (NonRec bndr' rhs' : binds)
  where
    occ = lookupLetOccInfo body_uds bndr
    
occAnalRec env lvl (CyclicSCC details_s) (WUD body_uds binds)
  | not (any needed details_s)
  = WUD body_uds binds
  | otherwise
  = WUD final_uds (Rec pairs : binds)
  where
    needed (ND { nd_bndr = bndr }) = isExportedId bndr || bndr `elemVarEnv` body_env
    body_env = ud_env body_uds

    WUD final_uds loop_breaker_nodes = mkLoopBreakerNodes env lvl body_uds details_s

    pairs = reOrderNodes 0 loop_breaker_nodes []

{- *********************************************************************
*                                                                      *
                Loop breaking
*                                                                      *
********************************************************************* -}

type Binding = (Id Zk, CoreExpr)

loopBreakNodes
  :: Int
  -> [LoopBreakerNode]
  -> [Binding]
  -> [Binding]
loopBreakNodes depth nodes binds
  = go (stronglyConnCompFromEdgedVerticesUniqR nodes)
  where
    go [] = binds
    go (scc:sccs) = loop_break_scc scc (go sccs)

    loop_break_scc scc binds
      = case scc of
          AcyclicSCC node -> nodeBinding mk_non_loop_breaker node : binds
          CyclicSCC nodes -> reOrderNodes depth nodes binds

reOrderNodes :: Int -> [LoopBreakerNode] -> [Binding] -> [Binding]
reOrderNodes _ [] _ = panic "reOrderNodes"
reOrderNodes _ [node] binds = nodeBinding mk_loop_breaker node : binds
reOrderNodes depth (node : nodes) binds
  = loopBreakNodes new_depth unchosen
    (map (nodeBinding mk_loop_breaker) chosen_nodes ++ binds)
  where
    (chosen_nodes, unchosen) = chooseLoopBreaker approximate_lb
                                                 (snd_score (node_payload node))
                                                 [node] [] nodes

    approximate_lb = depth >= 2
    new_depth | approximate_lb = 0
              | otherwise = depth + 1

nodeBinding :: (CoreId -> CoreId) -> LoopBreakerNode -> Binding
nodeBinding set_id_occ (node_payload -> SND { snd_bndr = bndr, snd_rhs = rhs })
  = (set_id_occ bndr, rhs)

mk_loop_breaker :: CoreId -> CoreId
mk_loop_breaker bndr = bndr `setIdOccInfo` occ'
  where
    occ' = strongLoopBreaker { occ_tail = tail_info }
    tail_info = tailCallInfo (idOccInfo bndr)

mk_non_loop_breaker :: CoreId -> CoreId
mk_non_loop_breaker bndr = bndr

chooseLoopBreaker
  :: Bool
  -> NodeScore
  -> [LoopBreakerNode]
  -> [LoopBreakerNode]
  -> [LoopBreakerNode]
  -> ([LoopBreakerNode], [LoopBreakerNode])
chooseLoopBreaker _ _ loop_nodes acc []
  = (loop_nodes, acc)

chooseLoopBreaker approx_lb loop_sc loop_nodes acc (node : nodes)
  | approx_lb
  , rank sc == rank loop_sc
  = chooseLoopBreaker approx_lb loop_sc (node : loop_nodes) acc nodes

  | sc `betterLB` loop_sc
  = chooseLoopBreaker approx_lb sc [node] (loop_nodes ++ acc) nodes

  | otherwise
  = chooseLoopBreaker approx_lb loop_sc loop_nodes (node : acc) nodes
  where
    sc = snd_score (node_payload node)

{- *********************************************************************
*                                                                      *
                   Making nodes
*                                                                      *
********************************************************************* -}

type LetrecNode = Node Unique NodeDetails

data NodeDetails = ND
  { nd_bndr :: Id Zk
  , nd_rhs :: !(WithTailUsageDetails CoreExpr)
  , nd_inl :: IdSet Zk
  }

instance Outputable NodeDetails where
  ppr nd = text "ND" <> braces
           (sep [ text "bndr =" <+> ppr (nd_bndr nd)
                , text "uds =" <+> ppr uds
                , text "inl =" <+> ppr (nd_inl nd)
                ])
    where WTUD uds _ = nd_rhs nd

type LoopBreakerNode = Node Unique SimpleNodeDetails

data SimpleNodeDetails = SND
  { snd_bndr :: IdWithOccInfo
  , snd_rhs :: CoreExpr
  , snd_score :: NodeScore
  }

instance Outputable SimpleNodeDetails where
  ppr nd = text "SND" <> braces
           (sep [ text "bndr =" <+> ppr (snd_bndr nd)
                , text "score =" <+> ppr (snd_score nd)
                ])

type NodeScore = (Int, Int, Bool)

rank :: NodeScore -> Int
rank (r, _, _) = r

makeNode
  :: OccEnv
  -> IdSet Zk
  -> (Id Zk, CoreExpr)
  -> LetrecNode
makeNode !env bndr_set (bndr, rhs)
  = DigraphNode { node_payload = details
                , node_key = varUnique bndr
                , node_dependencies = nonDetKeysUniqSet scope_fvs }
  where
    details = ND { nd_bndr = bndr'
                 , nd_rhs = WTUD (TUD rhs_ja unadj_scope_uds) rhs'
                 , nd_inl = inl_fvs
                 }

    bndr' | noBinderSwaps env = bndr
          | otherwise = bndr `setIdUnfolding` unf'

    unadj_inl_uds = unadj_rhs_uds `andUDs` adj_unf_uds
    unadj_scope_uds = unadj_inl_uds

    scope_fvs = udFreeVars bndr_set unadj_scope_uds

    inl_fvs = udFreeVars bndr_set unadj_inl_uds

    rhs_env = mkRhsOccEnv env Recursive OccRhs (idJoinPointHood bndr) bndr rhs

    WTUD ( TUD rhs_ja unadj_rhs_uds) rhs' = occAnalLamTail rhs_env rhs

    unf = realIdUnfolding bndr

    WTUD unf_tuds unf' = occAnalUnfolding rhs_env unf
    adj_unf_uds = adjustTailArity (JoinPoint rhs_ja) unf_tuds

mkLoopBreakerNodes
  :: OccEnv
  -> TopLevelFlag
  -> UsageDetails
  -> [NodeDetails]
  -> WithUsageDetails [LoopBreakerNode]
mkLoopBreakerNodes !env lvl body_uds details_s
  = WUD final_uds (zipWithEqual "mkLoopBreakerNodes" mk_lb_node details_s bndrs')
  where
    WUD final_uds bndrs' = tagRecBinders lvl body_uds details_s

    mk_lb_node nd@(ND { nd_bndr = old_bndr, nd_inl = inl_fvs, nd_rhs = WTUD _ rhs }) new_bndr
      = DigraphNode { node_payload = simple_nd
                    , node_key = varUnique old_bndr
                    , node_dependencies = nonDetKeysUniqSet inl_fvs }
      where
        simple_nd = SND { snd_bndr = new_bndr, snd_rhs = rhs, snd_score = score }
        score = nodeScore env new_bndr inl_fvs nd

nodeScore
  :: OccEnv
  -> Id Zk
  -> IdSet Zk
  -> NodeDetails
  -> NodeScore
nodeScore !env new_bndr lb_deps (ND { nd_bndr = old_bndr, nd_rhs = WTUD _ bind_rhs })
  | old_bndr `elemVarSet` lb_deps
  = (0, 0, True)

  | not (occ_unf_act env old_bndr)
  = (0, 0, True)

  | exprIsTrivial rhs
  = mk_score 10

  | CoreUnfolding { uf_guidance = UnfWhen {} } <- old_unf
  = mk_score 6

  | is_con_app rhs
  = mk_score 5

  | isStableUnfolding old_unf
  , can_unfold
  = mk_score 3

  | isOneOcc (idOccInfo new_bndr)
  = mk_score 2

  | can_unfold
  = mk_score 1

  | otherwise
  = (0, 0, is_lb)

  where
    mk_score :: Int -> NodeScore
    mk_score rank = (rank, rhs_size, is_lb)

    is_lb = isStrongLoopBreaker (idOccInfo old_bndr)

    old_unf = realIdUnfolding old_bndr
    can_unfold = canUnfold old_unf
    rhs = case old_unf of
            CoreUnfolding { uf_src = src, uf_tmpl = unf_rhs }
              | isStableSource src
                -> unf_rhs
            _ -> bind_rhs

    rhs_size = case old_unf of
                 CoreUnfolding { uf_guidance = guidance }
                   | UnfIfGoodArgs { ug_size = size } <- guidance
                     -> size
                 _ -> cheapExprSize rhs

    is_con_app (Var v) = isConLikeId v
    is_con_app (App f _) = is_con_app f
    is_con_app (Lam _ _ e) = is_con_app e
    is_con_app (Tick _ e) = is_con_app e
    is_con_app (Let _ e) = is_con_app e
    is_con_app _ = False

maxExprSize :: Int
maxExprSize = 20

cheapExprSize :: CoreExpr -> Int
cheapExprSize e = go 0 e
  where
    go n e | n >= maxExprSize = n
           | otherwise = go1 n e

    go1 n (Var {}) = n + 1
    go1 n (Lit {}) = n + 1
    go1 n (Type {}) = n
    go1 n (KiCo {}) = n
    go1 n (Kind {}) = n
    go1 n (Tick _ e) = go1 n e
    go1 n (Cast e _) = go1 n e
    go1 n (App f a) = go (go1 n f) a
    go1 n (Lam b _ e)
      | isRuntimeVar b = go (n + 1) e
      | otherwise = go1 n e
    go1 n (Let b e) = gos (go1 n e) (rhssOfBind b)
    go1 n (Case e _ _ as) = gos (go1 n e) (rhssOfAlts as)

    gos n [] = n
    gos n (e:es) | n >= maxExprSize = n
                 | otherwise = gos (go1 n e) es

betterLB :: NodeScore -> NodeScore -> Bool
betterLB (rank1, size1, lb1) (rank2, size2, _)
  | rank1 < rank2 = True
  | rank1 > rank2 = False
  | size1 < size2 = False
  | size1 > size2 = True
  | lb1 = True
  | otherwise = False

{- *********************************************************************
*                                                                      *
                Lambda groups
*                                                                      *
********************************************************************* -}

isOneShotFun :: CoreExpr -> Bool
isOneShotFun (Lam b _ e) = isOneShotBndr b && isOneShotFun e
isOneShotFun (Cast e _) = isOneShotFun e
isOneShotFun _ = True

occAnalLamTail :: OccEnv -> CoreExpr -> WithTailUsageDetails CoreExpr
occAnalLamTail env expr
  = let !(WUD usage expr') = occ_anal_lam_tail env expr
    in WTUD (TUD (joinRhsArity expr) usage) expr'

occ_anal_lam_tail :: OccEnv -> CoreExpr -> WithUsageDetails CoreExpr
occ_anal_lam_tail env expr@(Lam {}) = go env [] expr
  where
    go :: OccEnv -> [(CoreBndr, Maybe (MonoKind Zk))] -> CoreExpr -> WithUsageDetails CoreExpr
    go env rev_bndrs (Lam bndr mki body)
      | Core.Id id <- bndr --isRunTimeVar
      = let (env_one_shots', bndr') = case occ_one_shots env of
                                        [] -> ([], bndr)
                                        (os:oss) -> (oss, Core.Id $ updOneShotInfo id os)
            env' = env { occ_encl = OccVanilla, occ_one_shots = env_one_shots' }
        in go env' ((bndr', mki) : rev_bndrs) body
      | otherwise
      = go env ((bndr, mki) : rev_bndrs) body
    go env rev_bndrs body
      = addInScope env (id_bndrs rev_bndrs) $ \env ->
        let !(WUD usage body') = occ_anal_lam_tail env body
            wrap_lam body (bndr, mki) = Lam (tagLamBinder usage bndr) mki body
        in WUD (usage {-TODO `addLamCoVarOccs` rev_bndrs-})
               (foldl' wrap_lam body' rev_bndrs)
      where
        id_bndrs = mapMaybe $ \(bndr, _) -> case bndr of
                                              Core.Id id -> Just id
                                              _ -> Nothing
occ_anal_lam_tail env (Cast expr co)
  = let WUD usage expr' = occ_anal_lam_tail env expr
        {-TODO usage1 = addManyOccs usage (coVarsOfTyCo co)-}
        usage1 = usage
        usage2 = case expr of
                   Var{} | isRhsEnv env -> markAllMany usage1
                   _ -> usage1
        usage3 = markAllNonTail usage2
    in WUD usage3 (Cast expr' co)

occ_anal_lam_tail env expr = occAnal env expr

{- *********************************************************************
*                                                                      *
                Right hand sides
*                                                                      *
********************************************************************* -}

occAnalUnfolding :: OccEnv -> Unfolding -> WithTailUsageDetails Unfolding
occAnalUnfolding !env unf
  = case unf of
      CoreUnfolding { uf_tmpl = rhs, uf_src = src }
        | isStableSource src -> let WTUD (TUD rhs_ja uds) rhs' = occAnalLamTail env rhs
                                    unf' = unf { uf_tmpl = rhs' }
                                in WTUD (TUD rhs_ja (markAllMany uds)) unf'
        | otherwise -> WTUD (TUD 0 emptyDetails) unf

      _ -> WTUD (TUD 0 emptyDetails) unf

{- *********************************************************************
*                                                                      *
                Expressions
*                                                                      *
********************************************************************* -}

occAnal :: OccEnv -> CoreExpr -> WithUsageDetails CoreExpr

occAnal !_ expr@(Lit _) = WUD emptyDetails expr

occAnal env expr@(Var _) = occAnalApp env (expr, [], [])

occAnal _ expr@(Type ty) = panic "dunno"
occAnal _ expr@(KiCo kco) = panic "dunno"
occAnal _ expr@(Kind ki) = panic "dunno"

occAnal env (Tick tickish body) = WUD usage' (Tick tickish body')
  where
    WUD usage body' = occAnal env body
    usage' | tickish `tickishScopesLike` SoftScope = usage
           | otherwise = panic "currently unreachabel"

occAnal env (Cast expr co)
  = let (WUD usage expr') = occAnal env expr
    in panic "dunno"

occAnal env app@(App _ _) = occAnalApp env (collectArgsTicks tickishFloatable app)

occAnal env expr@(Lam {})
  = adjustNonRecRhs NotJoinPoint $ occAnalLamTail env expr

occAnal env _ = panic "unfinished"

occAnalArgs :: OccEnv -> CoreExpr -> [CoreExpr] -> [OneShots] -> WithUsageDetails CoreExpr
occAnalArgs !env fun args !one_shots = go emptyDetails fun args one_shots
  where
    env_args = setNonTailCtxt encl env

    encl | Var f <- fun, isDeadEndSig (idDmdSig f) = OccScrut
         | otherwise = OccVanilla

    go uds fun [] _ = WUD uds fun
    go uds fun (arg:args) one_shots
      = go (uds `andUDs` arg_uds) (fun `App` arg') args one_shots'
      where
        !(WUD arg_uds arg') = occAnal arg_env arg
        !(arg_env, one_shots')
          | isNonValArg arg
          = (env_args, one_shots)
          | otherwise
          = case one_shots of
              [] -> (env_args, [])
              (os:one_shots') -> (setOneShots os env_args, one_shots')

occAnalApp :: OccEnv -> (CoreExpr, [CoreArg], [CoreTickish]) -> WithUsageDetails CoreExpr
occAnalApp !env (Var fun_id, args, ticks)
  = WUD all_uds (mkTicks ticks app')
  where
    !(fun', fun_id') = lookupBndrSwap env fun_id
    !(WUD args_uds app') = occAnalArgs env fun' args one_shots

    fun_uds = mkOneOcc env fun_id' int_cxt n_args

    all_uds = fun_uds `andUDs` final_args_uds

    !final_args_uds = markAllNonTail $
                      markAllInsideLamIf (isRhsEnv env && is_exp) $
                      args_uds

    !n_val_args = valArgCount args
    !n_args = length args
    !int_cxt = case occ_encl env of
                 OccScrut -> IsInteresting
                 _ | n_val_args > 0 -> IsInteresting
                   | otherwise -> NotInteresting

    !is_exp = isExpandableApp fun_id n_val_args

    one_shots = argsOneShots (idDmdSig fun_id) guaranteed_val_args
    guaranteed_val_args = n_val_args + length (takeWhile isOneShotInfo (occ_one_shots env))

occAnalApp env (fun, args, ticks)
  = WUD (markAllNonTail (fun_uds `andUDs` args_uds)) (mkTicks ticks app')
  where
    !(WUD args_uds app') = occAnalArgs env fun' args []
    !(WUD fun_uds fun') = occAnal (addAppCtxt env args) fun

addAppCtxt :: OccEnv -> [CoreArg] -> OccEnv
addAppCtxt env@(OccEnv { occ_one_shots = ctxt }) args
  | n_val_args > 0
  = env { occ_one_shots = replicate n_val_args OneShotLam ++ ctxt
        , occ_encl = OccVanilla }
  | otherwise
  = env
  where
    n_val_args = valArgCount args

{- *********************************************************************
*                                                                      *
                OccEnv
*                                                                      *
********************************************************************* -}

data OccEnv = OccEnv
  { occ_encl :: !OccEncl
  , occ_one_shots :: !OneShots
  , occ_unf_act :: Id Zk -> Bool
  , occ_bs_env :: !(VarEnv InId (OutId, Maybe (TypeCoercion Zk)))
  , occ_bs_rng :: !(IdSet Zk)
  , occ_join_points :: !JoinPointInfo
  }

type JoinPointInfo = VarEnv (Id Zk) OccInfoEnv

data OccEncl
  = OccRhs
  | OccScrut
  | OccVanilla

instance Outputable OccEncl where
  ppr OccRhs = text "occRhs"
  ppr OccScrut = text "occScrut"
  ppr OccVanilla = text "occVanilla"

type OneShots = [OneShotInfo]
 
initOccEnv :: OccEnv
initOccEnv = OccEnv { occ_encl = OccVanilla
                    , occ_one_shots = []
                    , occ_unf_act = \_ -> True
                    , occ_join_points = emptyVarEnv
                    , occ_bs_env = emptyVarEnv
                    , occ_bs_rng = emptyVarSet }

noBinderSwaps :: OccEnv -> Bool
noBinderSwaps (OccEnv { occ_bs_env = bs_env }) = isEmptyVarEnv bs_env

setNonTailCtxt :: OccEncl -> OccEnv -> OccEnv
setNonTailCtxt ctxt !env = env { occ_encl = ctxt
                               , occ_one_shots = []
                               , occ_join_points = zapJoinPointInfo (occ_join_points env) }

mkRhsOccEnv :: OccEnv -> RecFlag -> OccEncl -> JoinPointHood -> CoreId -> CoreExpr -> OccEnv
mkRhsOccEnv env@(OccEnv { occ_one_shots = ctxt_one_shots, occ_join_points = ctxt_join_points })
            is_rec encl jp_hood bndr rhs
  | JoinPoint join_arity <- jp_hood
  = env { occ_encl = OccVanilla
        , occ_one_shots = extendOneShotsForJoinPoint is_rec join_arity rhs ctxt_one_shots
        , occ_join_points = ctxt_join_points }
  | otherwise
  = env { occ_encl = encl
        , occ_one_shots = argOneShots (idDemandInfo bndr)
        , occ_join_points = zapJoinPointInfo ctxt_join_points }

zapJoinPointInfo :: JoinPointInfo -> JoinPointInfo
zapJoinPointInfo info | debugIsOn = mapVarEnv (\_ -> emptyVarEnv) info
                      | otherwise = emptyVarEnv

extendOneShotsForJoinPoint
  :: RecFlag
  -> JoinArity
  -> CoreExpr
  -> [OneShotInfo]
  -> [OneShotInfo]
extendOneShotsForJoinPoint is_rec join_arity rhs ctxt_one_shots
  = go join_arity rhs
  where
    os = case is_rec of
           NonRecursive -> OneShotLam
           Recursive -> NoOneShotInfo

    go 0 _ = ctxt_one_shots
    go n (Lam b _ rhs)
      | Core.Id _ <- b = os : go (n - 1) rhs
      | otherwise = go (n - 1) rhs
    go _ _ = []

setOneShots :: OneShots -> OccEnv -> OccEnv
setOneShots os !env
  | null os = env
  | otherwise = env { occ_one_shots = os }

isRhsEnv :: OccEnv -> Bool
isRhsEnv (OccEnv { occ_encl = cxt }) = case cxt of
                                         OccRhs -> True
                                         _ -> False

addInScopeList
  :: OccEnv
  -> [CoreId]
  -> (OccEnv -> WithUsageDetails a)
  -> WithUsageDetails a
{-# INLINE addInScopeList #-}
addInScopeList env bndrs thing_inside
  | null bndrs = thing_inside env
  | otherwise = addInScope env bndrs thing_inside

addInScopeOne :: OccEnv -> CoreId -> (OccEnv -> WithUsageDetails a) -> WithUsageDetails a
{-# INLINE addInScopeOne #-}
addInScopeOne env bndr = addInScope env [bndr]

{-# INLINE addInScope #-}
addInScope :: OccEnv -> [CoreId] -> (OccEnv -> WithUsageDetails a) -> WithUsageDetails a
addInScope env bndrs thing_inside
  | isEmptyVarEnv (occ_bs_env env)
  , isEmptyVarEnv (occ_join_points env)
  , WUD uds res <- thing_inside env
  = WUD (delBndrsFromUDs bndrs uds) res

addInScope env bndrs thing_inside = WUD uds' res
  where
    bndr_set = mkVarSet bndrs
    !(env', bad_joins) = preprocess_env env bndr_set
    !(WUD uds res) = thing_inside env'
    uds' = postprocess_uds bndrs bad_joins uds

preprocess_env :: OccEnv -> IdSet Zk -> (OccEnv, JoinPointInfo)
preprocess_env env@(OccEnv { occ_join_points = join_points, occ_bs_rng = bs_rng_vars }) bndr_set
  | bad_joins = (drop_shadowed_swaps (drop_shadowed_joins env), join_points)
  | otherwise = (drop_shadowed_swaps env, emptyVarEnv)
  where
    drop_shadowed_swaps env@(OccEnv { occ_bs_env = swap_env })
      | isEmptyVarEnv swap_env
      = env
      | bs_rng_vars `intersectsVarSet` bndr_set
      = env { occ_bs_env = emptyVarEnv, occ_bs_rng = emptyVarSet }
      | otherwise
      = env { occ_bs_env = swap_env `minusUFM` bndr_fm }

    drop_shadowed_joins env = env { occ_join_points = emptyVarEnv }

    bad_joins = nonDetStrictFoldVarEnv_Directly is_bad False join_points

    bndr_fm = getUniqSet bndr_set

    is_bad uniq join_uds rest
      = uniq `elemUniqSet_Directly` bndr_set
        || not (bndr_fm `disjointUFM` join_uds)
        || rest

postprocess_uds :: [Id Zk] -> JoinPointInfo -> UsageDetails -> UsageDetails
postprocess_uds bndrs bad_joins uds
  = add_bad_joins (delBndrsFromUDs bndrs uds)
  where
    add_bad_joins uds
      | isEmptyVarEnv bad_joins = uds
      | otherwise = modifyUDEnv extend_with_bad_joins uds

    extend_with_bad_joins env = nonDetStrictFoldUFM_Directly add_bad_join env bad_joins

    add_bad_join uniq join_env env
      | uniq `elemVarEnvByKey` env = plusVarEnv_C andLocalOcc env join_env
      | otherwise = env

addJoinPoint :: OccEnv -> CoreId -> UsageDetails -> OccEnv
addJoinPoint env bndr rhs_uds
  | isEmptyVarEnv zeroed_form
  = env
  | otherwise
  = env { occ_join_points = extendVarEnv (occ_join_points env) bndr zeroed_form }
  where
    zeroed_form = mkZeroedForm rhs_uds

mkZeroedForm :: UsageDetails -> OccInfoEnv
mkZeroedForm (UD { ud_env = rhs_occs })
  = mapMaybeUFM do_one rhs_occs
  where
    do_one :: LocalOcc -> Maybe LocalOcc
    do_one (ManyOccL {}) = Nothing
    do_one occ@(OneOccL {}) = Just (occ { lo_n_br = 0 })

{- *********************************************************************
*                                                                      *
                    Binder swap
*                                                                      *
********************************************************************* -}

lookupBndrSwap :: OccEnv -> Id Zk -> (CoreExpr, Id Zk)
lookupBndrSwap env@(OccEnv { occ_bs_env = bs_env }) bndr
  = case lookupVarEnv bs_env bndr of
      Nothing -> (Var bndr, bndr)
      Just (bndr1, mco) -> case lookupBndrSwap env bndr1 of
                             (fun, fun_id) -> (mkCastMCo fun mco, fun_id)

{- *********************************************************************
*                                                                      *
                OccEnv
*                                                                      *
********************************************************************* -}

type OccInfoEnv = VarEnv (Id Zk) LocalOcc

data LocalOcc
  = OneOccL
    { lo_n_br :: {-# UNPACK #-} !BranchCount
    , lo_tail :: !TailCallInfo
    , lo_int_cxt :: !InterestingCxt }
  | ManyOccL !TailCallInfo

instance Outputable LocalOcc where
  ppr (OneOccL { lo_n_br = n, lo_tail = tci })
    = text "OneOccL" <> braces (ppr n <> comma <> ppr tci)
  ppr (ManyOccL tci) = text "ManyOccL" <> braces (ppr tci)

localTailCallInfo :: LocalOcc -> TailCallInfo
localTailCallInfo (OneOccL { lo_tail = tci }) = tci
localTailCallInfo (ManyOccL tci) = tci

type ZappedSet = OccInfoEnv

data UsageDetails = UD
  { ud_env :: !OccInfoEnv
  , ud_z_many :: !ZappedSet
  , ud_z_in_lam :: !ZappedSet
  , ud_z_tail :: !ZappedSet
  }

instance Outputable UsageDetails where
  ppr ud@(UD { ud_env = env, ud_z_tail = z_tail })
    = text "UD" <+> (braces $ fsep $ punctuate comma $
                     [ ppr uq <+> text ":->" <+> ppr (lookupOccInfoByUnique ud uq)
                     | (uq, _) <- nonDetStrictFoldVarEnv_Directly do_one [] env ])
      $$ nest 2 (text "ud_z_tail" <+> ppr z_tail)
    where
      do_one uniq occ occs = (uniq, occ) : occs

data TailUsageDetails = TUD !JoinArity !UsageDetails

instance Outputable TailUsageDetails where
  ppr (TUD ja uds) = lambda <> ppr ja <> ppr uds

data WithUsageDetails a = WUD !UsageDetails !a
data WithTailUsageDetails a = WTUD !TailUsageDetails !a

andUDs :: UsageDetails -> UsageDetails -> UsageDetails
andUDs = combineUsageDetailsWith andLocalOcc

orUDs :: UsageDetails -> UsageDetails -> UsageDetails
orUDs = combineUsageDetailsWith orLocalOcc

mkOneOcc :: OccEnv -> Id Zk -> InterestingCxt -> JoinArity -> UsageDetails
mkOneOcc !env id int_cxt arity
  | not (isLocalId id)
  = emptyDetails
  | Just join_uds <- lookupVarEnv (occ_join_points env) id
  = assertPpr (not (isEmptyVarEnv join_uds)) (ppr id) $
    mkSimpleDetails (extendVarEnv join_uds id occ)
  | otherwise
  = mkSimpleDetails (unitVarEnv id occ)
  where
    occ = OneOccL { lo_n_br = 1
                  , lo_int_cxt = int_cxt
                  , lo_tail = AlwaysTailCalled arity }

emptyDetails :: UsageDetails
emptyDetails = mkSimpleDetails emptyVarEnv

isEmptyDetails :: UsageDetails -> Bool
isEmptyDetails (UD { ud_env = env }) = isEmptyVarEnv env

mkSimpleDetails :: OccInfoEnv -> UsageDetails
mkSimpleDetails env = UD { ud_env = env
                         , ud_z_many = emptyVarEnv
                         , ud_z_in_lam = emptyVarEnv
                         , ud_z_tail = emptyVarEnv }

modifyUDEnv :: (OccInfoEnv -> OccInfoEnv) -> UsageDetails -> UsageDetails
modifyUDEnv f uds@(UD { ud_env = env }) = uds { ud_env = f env }

delBndrsFromUDs :: [Id Zk] -> UsageDetails -> UsageDetails
delBndrsFromUDs bndrs (UD { ud_env = env
                          , ud_z_many = z_many
                          , ud_z_in_lam = z_in_lam
                          , ud_z_tail = z_tail })
  = UD { ud_env = env `delVarEnvList` bndrs
       , ud_z_many = z_many `delVarEnvList` bndrs
       , ud_z_in_lam = z_in_lam `delVarEnvList` bndrs
       , ud_z_tail = z_tail `delVarEnvList` bndrs }

markAllMany :: UsageDetails -> UsageDetails
markAllMany ud@(UD { ud_env = env }) = ud { ud_z_many = env }

markAllInsideLam :: UsageDetails -> UsageDetails
markAllInsideLam ud@(UD { ud_env = env }) = ud { ud_z_in_lam = env }

markAllNonTail :: UsageDetails -> UsageDetails
markAllNonTail ud@(UD { ud_env = env }) = ud { ud_z_tail = env }

markAllInsideLamIf :: Bool -> UsageDetails -> UsageDetails
markAllInsideLamIf True ud = markAllInsideLam ud
markAllInsideLamIf False ud = ud

markAllNonTailIf :: Bool -> UsageDetails -> UsageDetails
markAllNonTailIf True ud = markAllNonTail ud
markAllNonTailIf False ud = ud
 
lookupTailCallInfo :: UsageDetails -> CoreId -> TailCallInfo
lookupTailCallInfo uds id
  | UD { ud_z_tail = z_tail, ud_env = env } <- uds
  , not (id `elemVarEnv` z_tail)
  , Just occ <- lookupVarEnv env id
  = localTailCallInfo occ
  | otherwise
  = NoTailCallInfo

udFreeVars :: IdSet Zk -> UsageDetails -> IdSet Zk
udFreeVars bndrs (UD { ud_env = env }) = restrictFreeVars bndrs env

restrictFreeVars :: IdSet Zk -> OccInfoEnv -> IdSet Zk
restrictFreeVars bndrs fvs = restrictUniqSetToUFM bndrs fvs

{-# INLINE combineUsageDetailsWith #-}
combineUsageDetailsWith
  :: (LocalOcc -> LocalOcc -> LocalOcc) -> UsageDetails -> UsageDetails -> UsageDetails
combineUsageDetailsWith plus_occ_info
  uds1@(UD { ud_env = env1, ud_z_many = z_many1, ud_z_in_lam = z_in_lam1, ud_z_tail = z_tail1 })
  uds2@(UD { ud_env = env2, ud_z_many = z_many2, ud_z_in_lam = z_in_lam2, ud_z_tail = z_tail2 })
  | isEmptyVarEnv env1 = uds2
  | isEmptyVarEnv env2 = uds1
  | otherwise
  = UD { ud_env = plusVarEnv_C plus_occ_info env1 env2
       , ud_z_many = plusVarEnv z_many1 z_many2
       , ud_z_in_lam = plusVarEnv z_in_lam1 z_in_lam2
       , ud_z_tail = plusVarEnv z_tail1 z_tail2 }

lookupLetOccInfo :: UsageDetails -> CoreId -> OccInfo
lookupLetOccInfo ud id
  | isExportedId id = noOccInfo
  | otherwise = lookupOccInfoByUnique ud (varUnique id)

lookupOccInfo :: UsageDetails -> Id Zk -> OccInfo
lookupOccInfo ud id = lookupOccInfoByUnique ud (varUnique id)

lookupOccInfoByUnique :: UsageDetails -> Unique -> OccInfo
lookupOccInfoByUnique (UD { ud_env = env
                          , ud_z_many = z_many
                          , ud_z_in_lam = z_in_lam
                          , ud_z_tail = z_tail })
                      uniq
  = case lookupVarEnv_Directly env uniq of
      Nothing -> IAmDead
      Just (OneOccL { lo_n_br = n_br, lo_int_cxt = int_cxt, lo_tail = tail_info })
        | uniq `elemVarEnvByKey` z_many
          -> ManyOccs { occ_tail = mk_tail_info tail_info }
        | otherwise
          -> OneOcc { occ_in_lam = in_lam
                    , occ_n_br = n_br
                    , occ_int_cxt = int_cxt
                    , occ_tail = mk_tail_info tail_info }
        where in_lam | uniq `elemVarEnvByKey` z_in_lam = IsInsideLam
                     | otherwise = NotInsideLam
      Just (ManyOccL tail_info) -> ManyOccs { occ_tail = mk_tail_info tail_info }
  where
    mk_tail_info ti
      | uniq `elemVarEnvByKey` z_tail = NoTailCallInfo
      | otherwise = ti

adjustNonRecRhs :: JoinPointHood -> WithTailUsageDetails CoreExpr -> WithUsageDetails CoreExpr
adjustNonRecRhs mb_join_arity rhs_wuds@(WTUD _ rhs)
  = WUD (adjustTailUsage mb_join_arity rhs_wuds) rhs

adjustTailUsage :: JoinPointHood -> WithTailUsageDetails CoreExpr -> UsageDetails
adjustTailUsage mb_join_arity (WTUD (TUD rhs_ja uds) rhs)
  = markAllInsideLamIf (not one_shot) $
    markAllNonTailIf (not exact_join) $
    uds
  where
    one_shot = isOneShotFun rhs
    exact_join = mb_join_arity == JoinPoint rhs_ja

adjustTailArity :: JoinPointHood -> TailUsageDetails -> UsageDetails
adjustTailArity mb_rhs_ja (TUD ja usage)
  = markAllNonTailIf (mb_rhs_ja /= JoinPoint ja) usage

type IdWithOccInfo = Id Zk

tagLamBinders :: UsageDetails -> [CoreBndr] -> [CoreBndr]
tagLamBinders usage binders = map (tagLamBinder usage) binders

tagLamBinder :: UsageDetails -> CoreBndr -> CoreBndr
tagLamBinder usage (Core.Id bndr) = Core.Id $ setBinderOcc (markNonTail occ) bndr
  where occ = lookupOccInfo usage bndr
tagLamBinder _ bndr = bndr

tagNonRecBinder
  :: TopLevelFlag
  -> OccInfo
  -> CoreId
  -> (IdWithOccInfo, JoinPointHood)
tagNonRecBinder lvl occ bndr
  | okForJoinPoint lvl bndr tail_call_info
  , AlwaysTailCalled ar <- tail_call_info
  = (setBinderOcc occ bndr, JoinPoint ar)
  | otherwise
  = (setBinderOcc zapped_occ bndr, NotJoinPoint)
  where
    tail_call_info = tailCallInfo occ
    zapped_occ = markNonTail occ

tagRecBinders
  :: TopLevelFlag
  -> UsageDetails
  -> [NodeDetails]
  -> WithUsageDetails [IdWithOccInfo]
tagRecBinders lvl body_uds details_s
  = let bndrs = map nd_bndr details_s

        unadj_uds = foldr (andUDs . test_manifest_arity) body_uds details_s
        test_manifest_arity ND { nd_rhs = WTUD tuds rhs }
          = adjustTailArity (JoinPoint (joinRhsArity rhs)) tuds

        will_be_joins = decideRecJoinPointHood lvl unadj_uds bndrs

        mb_join_arity :: CoreId -> JoinPointHood
        mb_join_arity bndr
          | will_be_joins
          , AlwaysTailCalled arity <- lookupTailCallInfo unadj_uds bndr
          = JoinPoint arity
          | otherwise
          = assert (not will_be_joins)
            NotJoinPoint

        rhs_udss' = [ adjustTailUsage (mb_join_arity bndr) rhs_wuds
                    | ND { nd_bndr = bndr, nd_rhs = rhs_wuds } <- details_s ]

        adj_uds = foldr andUDs body_uds rhs_udss'

        bndrs' = [ setBinderOcc (lookupLetOccInfo adj_uds bndr) bndr
                 | bndr <- bndrs ]

    in WUD adj_uds bndrs'

setBinderOcc :: OccInfo -> Id Zk -> Id Zk
setBinderOcc occ_info bndr
  | occ_info == idOccInfo bndr = bndr
  | otherwise = setIdOccInfo bndr occ_info

decideRecJoinPointHood
  :: TopLevelFlag
  -> UsageDetails
  -> [CoreId]
  -> Bool
decideRecJoinPointHood lvl usage bndrs
  = all ok bndrs
  where
    ok bndr = okForJoinPoint lvl bndr (lookupTailCallInfo usage bndr)

okForJoinPoint :: TopLevelFlag -> CoreId -> TailCallInfo -> Bool
okForJoinPoint lvl bndr tail_call_info
  | isJoinId bndr
  = warnPprTrace lost_join "Lost join point" lost_join_doc $ True
  | valid_join
  = True
  | otherwise
  = False
  where
    valid_join
      | NotTopLevel <- lvl
      , AlwaysTailCalled arity <- tail_call_info
      , ok_unfolding arity (realIdUnfolding bndr)
      , panic "isValidJoinPointType arity (varType bndr)"
      = True
      | otherwise
      = False

    lost_join | JoinPoint ja <- idJoinPointHood bndr
              = not valid_join ||
                (case tail_call_info of
                   AlwaysTailCalled ja' -> ja /= ja'
                   _ -> False)
              | otherwise
              = False

    ok_unfolding join_arity (CoreUnfolding { uf_src = src, uf_tmpl = rhs })
      = not (isStableSource src && join_arity > joinRhsArity rhs)
    ok_unfolding _ _ = True

    lost_join_doc
      = vcat [ text "bndr:" <+> ppr bndr
             , text "tc:" <+> ppr tail_call_info
             , case tail_call_info of
                 AlwaysTailCalled arity ->
                   vcat [ text "ok_unf:" <+> ppr (ok_unfolding arity (realIdUnfolding bndr))
                        , text "ok_type:" <+> panic "ppr (isValidJoinPointType arity (varType bndr))" ]
                 _ -> empty ]

{- *********************************************************************
*                                                                      *
                    Operations over OccInfo
*                                                                      *
********************************************************************* -}

markNonTail :: OccInfo -> OccInfo
markNonTail IAmDead = IAmDead
markNonTail occ = occ { occ_tail = NoTailCallInfo }

andLocalOcc :: LocalOcc -> LocalOcc -> LocalOcc
andLocalOcc occ1 occ2 = ManyOccL (tci1 `andTailCallInfo` tci2)
  where
    !tci1 = localTailCallInfo occ1
    !tci2 = localTailCallInfo occ2

orLocalOcc :: LocalOcc -> LocalOcc -> LocalOcc
orLocalOcc (OneOccL { lo_n_br = nbr1, lo_int_cxt = int_cxt1, lo_tail = tci1 })
           (OneOccL { lo_n_br = nbr2, lo_int_cxt = int_cxt2, lo_tail = tci2 })
  = OneOccL { lo_n_br = nbr1 + nbr2
            , lo_int_cxt = int_cxt1 `mappend` int_cxt2
            , lo_tail = tci1 `andTailCallInfo` tci2 }
orLocalOcc occ1 occ2 = andLocalOcc occ1 occ2

andTailCallInfo :: TailCallInfo -> TailCallInfo -> TailCallInfo
andTailCallInfo info@(AlwaysTailCalled arity1) (AlwaysTailCalled arity2)
  | arity1 == arity2 = info
andTailCallInfo _ _ = NoTailCallInfo
