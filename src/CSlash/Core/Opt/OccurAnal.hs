{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -fmax-worker-args=122 #-}

module CSlash.Core.Opt.OccurAnal where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Core as Core
import CSlash.Core.FVs
import CSlash.Core.Utils   ( {-exprIsTrivial, isDefaultAlt,-} isExpandableApp,
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
import CSlash.Utils.Constants (debugIsOn)

-- import GHC.Builtin.Names( runRWKey )
import CSlash.Unit.Module( Module )

import Data.List (mapAccumL)
import Data.List.NonEmpty (NonEmpty (..))

occurAnalyzeExpr :: CoreExpr -> CoreExpr
occurAnalyzeExpr expr = expr'
  where WUD _ expr' = occAnal initOccEnv expr

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
    go :: OccEnv -> [(CoreBndr Zk, Maybe (MonoKind Zk))] -> CoreExpr -> WithUsageDetails CoreExpr
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

setNonTailCtxt :: OccEncl -> OccEnv -> OccEnv
setNonTailCtxt ctxt !env = env { occ_encl = ctxt
                               , occ_one_shots = []
                               , occ_join_points = zapJoinPointInfo (occ_join_points env) }

zapJoinPointInfo :: JoinPointInfo -> JoinPointInfo
zapJoinPointInfo info | debugIsOn = mapVarEnv (\_ -> emptyVarEnv) info
                      | otherwise = emptyVarEnv

setOneShots :: OneShots -> OccEnv -> OccEnv
setOneShots os !env
  | null os = env
  | otherwise = env { occ_one_shots = os }

isRhsEnv :: OccEnv -> Bool
isRhsEnv (OccEnv { occ_encl = cxt }) = case cxt of
                                         OccRhs -> True
                                         _ -> False

{-# INLINE addInScope #-}
addInScope :: OccEnv -> [Id Zk] -> (OccEnv -> WithUsageDetails a) -> WithUsageDetails a
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

tagLamBinders :: UsageDetails -> [CoreBndr Zk] -> [CoreBndr Zk]
tagLamBinders usage binders = map (tagLamBinder usage) binders

tagLamBinder :: UsageDetails -> CoreBndr Zk -> CoreBndr Zk
tagLamBinder usage (Core.Id bndr) = Core.Id $ setBinderOcc (markNonTail occ) bndr
  where occ = lookupOccInfo usage bndr
tagLamBinder _ bndr = bndr

setBinderOcc :: OccInfo -> Id Zk -> Id Zk
setBinderOcc occ_info bndr
  | occ_info == idOccInfo bndr = bndr
  | otherwise = setIdOccInfo bndr occ_info


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

andTailCallInfo :: TailCallInfo -> TailCallInfo -> TailCallInfo
andTailCallInfo info@(AlwaysTailCalled arity1) (AlwaysTailCalled arity2)
  | arity1 == arity2 = info
andTailCallInfo _ _ = NoTailCallInfo
