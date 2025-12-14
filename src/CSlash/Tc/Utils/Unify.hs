{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RecordWildCards #-}

module CSlash.Tc.Utils.Unify where

import Prelude hiding ((<>))

import CSlash.Cs

-- import GHC.Tc.Utils.Concrete ( hasFixedRuntimeRep, hasFixedRuntimeRep_syntactic )
import CSlash.Tc.Utils.Env
import CSlash.Tc.Utils.Instantiate
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Utils.TcMType
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.BasicTypes
import CSlash.Tc.Zonk.TcType

import CSlash.Core.Type
import CSlash.Core.Type.Rep
import CSlash.Core.Type.Compare (tcEqType)
import CSlash.Core.Type.Ppr (debugPprType, pprSigmaType)
import CSlash.Core.Type.FVs( isInjectiveInType )
import CSlash.Core.TyCon
-- import GHC.Core.Coercion
import CSlash.Core.Kind
import CSlash.Core.Kind.FVs
import CSlash.Core.Kind.Compare (tcEqKind, tcEqMonoKind)
import CSlash.Core.Reduction

import CSlash.Builtin.Types
import CSlash.Types.Name
-- import CSlash.Types.Id( idType )
import CSlash.Types.Var as Var
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Types.Basic
import CSlash.Types.Unique.Set (nonDetEltsUniqSet)

import CSlash.Utils.Error
import CSlash.Utils.Misc
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Trace

import CSlash.Driver.DynFlags
import CSlash.Data.Bag
import CSlash.Data.FastString( fsLit )

import Control.Monad
import Data.Monoid as DM ( Any(..) )
import qualified Data.Semigroup as S ( (<>) )

{- *********************************************************************
*                                                                      *
              matchActualFunTys
*                                                                      *
********************************************************************* -}

matchActualFunTy
  :: ExpectedFunTyOrigin
  -> Maybe TypedThing
  -> (Arity, AnyType)
  -> AnyRhoType
  -> TcM (AnyCsWrapper, AnySigmaType, AnySigmaType)
matchActualFunTy herald mb_thing err_info fun_ty
  = assertPpr (isRhoTy fun_ty) (ppr fun_ty)
    $ go fun_ty
  where
    go :: AnyRhoType -> TcM (AnyCsWrapper, AnySigmaType, AnySigmaType)

    go ty | Just ty' <- coreView ty = go ty'

    go (FunTy { ft_arg = arg_ty, ft_res = res_ty }) = return (idCsWrapper, arg_ty, res_ty)

    go ty@(TyVarTy tv)
      | Just mtv <- toTcTyVar_maybe tv
      , isMetaVar mtv
      = do cts <- readMetaTyVar mtv
           case cts of
             Indirect ty' -> go ty'
             Flexi -> defer ty

    go ty = addErrCtxtM (mk_ctxt ty) (defer ty)

    defer fun_ty = do
      (arg_ty, fun_ki) <- new_check_arg_ty_ki 1
      res_ty <- asAnyTyKi <$> newOpenFlexiTyVarTy
      let unif_fun_ty = mkFunTy fun_ki arg_ty res_ty
      co <- unifyType mb_thing fun_ty unif_fun_ty
      return (mkWpCast co, arg_ty, res_ty)

    mk_ctxt :: AnyType -> AnyTidyEnv -> ZonkM (AnyTidyEnv, SDoc)
    mk_ctxt _ = mkFunTysMsg herald err_info

{- *********************************************************************
*                                                                      *
          Skolemization and matchExpectedFunTys
*                                                                      *
********************************************************************* -}

tcSkolemizeGeneral
  :: UserTypeCtxt
  -> AnyType -> AnyType
  -> ([(Name, AnyKiVar)] -> [(Name, AnyTyVar AnyKiVar)] -> AnyType -> TcM result)
  -> TcM (AnyCsWrapper, result)
tcSkolemizeGeneral ctxt top_ty expected_ty thing_inside
  | isRhoTy expected_ty
  = do let sig_skol = SigSkol ctxt top_ty []
       result <- checkKiConstraints sig_skol [] [] $ thing_inside [] [] expected_ty
       return (idCsWrapper, result)

  | otherwise
  = do rec { (wrap, kv_prs, tv_prs, rho_ty) <- topSkolemize skol_info_ki skol_info expected_ty
           ; let sig_skol = SigSkol ctxt top_ty tv_prs
                 sig_skol_ki = SigSkolKi ctxt top_ty kv_prs
           ; skol_info <- mkSkolemInfo sig_skol 
           ; skol_info_ki <- mkSkolemInfo sig_skol_ki }
       let skol_kvs = map snd kv_prs
           skol_tvs = map snd tv_prs
       traceTc "tcSkolemizeGeneral" (pprUserTypeCtxt ctxt <+> ppr skol_kvs <+> ppr tv_prs)
       result <- checkTyKiConstraints sig_skol skol_kvs skol_tvs []
                 $ thing_inside kv_prs tv_prs rho_ty
       return (wrap, result)

tcSkolemizeCompleteSig
  :: TcCompleteSig
  -> ([ExpPatType] -> AnyRhoType -> TcM result)
  -> TcM (AnyCsWrapper, result)
tcSkolemizeCompleteSig (CSig { sig_bndr = poly_id, sig_ctxt = ctxt, sig_loc = loc })
                       thing_inside
  = do
  cur_loc <- getSrcSpanM
  let poly_ty = varType poly_id
  setSrcSpan loc $
    tcSkolemizeGeneral ctxt poly_ty poly_ty $ \ kv_prs tv_prs rho_ty ->
    setSrcSpan cur_loc
    $ tcExtendNameKiVarEnv kv_prs
    $ tcExtendNameTyVarEnv tv_prs
    $ thing_inside ((map (mkInvisExpPatKind . snd) kv_prs)
                    ++ (map (mkInvisExpPatType . snd) tv_prs))
                   rho_ty

tcSkolemizeExpectedType
  :: AnySigmaType
  -> ([ExpPatType] -> AnyRhoType -> TcM result)
  -> TcM (AnyCsWrapper, result)
tcSkolemizeExpectedType exp_ty thing_inside
  = tcSkolemizeGeneral GenSigCtxt exp_ty exp_ty $ \kv_prs tv_prs rho_ty ->
    thing_inside ((map (mkInvisExpPatKind . snd) kv_prs)
                  ++ (map (mkInvisExpPatType . snd) tv_prs))
                 rho_ty

tcSkolemize
  :: UserTypeCtxt
  -> AnySigmaType
  -> (AnyRhoType -> TcM result)
  -> TcM (AnyCsWrapper, result)
tcSkolemize ctxt expected_ty thing_inside
  = tcSkolemizeGeneral ctxt expected_ty expected_ty $ \_ _ rho_ty ->
    thing_inside rho_ty

checkTyKiConstraints
  :: SkolemInfoAnon
  -> [AnyKiVar]
  -> [AnyTyVar AnyKiVar]
  -> [KiCoVar AnyKiVar]
  -> TcM result
  -> TcM result
checkTyKiConstraints skol_info skol_kvs skol_tvs given thing_inside = do
  ty_implication_needed <- implicationNeeded skol_info skol_tvs
  ki_implication_needed <- kiImplicationNeeded skol_info skol_kvs given
  if ty_implication_needed || ki_implication_needed
    then do (tclvl, wanted, result) <- pushLevelAndCaptureConstraints thing_inside
            (kiImplics, tyImplics)
              <- buildTyKiImplicationFor tclvl skol_info skol_kvs skol_tvs given wanted
            traceTc "checkTyKiConstraints" (ppr tclvl $$ ppr skol_kvs $$ ppr skol_tvs)
            emitKiImplications kiImplics
            emitTyImplications tyImplics
            return result
    else thing_inside

checkTyConstraints :: SkolemInfoAnon -> [AnyTyVar AnyKiVar] -> TcM result -> TcM (result)
checkTyConstraints skol_info skol_tvs thing_inside = do
  implication_needed <- implicationNeeded skol_info skol_tvs
  if implication_needed
    then do (tclvl, wanted, result) <- pushLevelAndCaptureConstraints thing_inside
            implics <- buildTyImplicationFor tclvl skol_info skol_tvs wanted
            traceTc "checkTyConstraints" (ppr tclvl $$ ppr skol_tvs)
            emitTyImplications implics
            return result
    else thing_inside

checkKiConstraints
  :: SkolemInfoAnon -> [AnyKiVar] -> [KiCoVar AnyKiVar] -> TcM result -> TcM result
checkKiConstraints skol_info skol_kvs given thing_inside = do
  implication_needed <- kiImplicationNeeded skol_info skol_kvs given
  if implication_needed
    then do (tclvl, wanted, result) <- pushLevelAndCaptureConstraints thing_inside
            wanted <- case onlyWantedKiConstraints_maybe wanted of
                        Just w -> return w
                        _ -> pprPanic "checkKiConstraints has ty constraints" (ppr wanted)
            implics <- buildKiImplicationFor tclvl skol_info skol_kvs given wanted
            emitKiImplications implics
            return result
    else thing_inside

emitResidualKvConstraint :: SkolemInfo -> [TcKiVar] -> TcLevel -> WantedKiConstraints -> TcM ()
emitResidualKvConstraint skol_info skol_kvs tclvl wanted
  | not (isEmptyWC wanted)
    || checkTelescopeSkol skol_info_anon
  = do implic <- buildKvImplication skol_info_anon skol_kvs tclvl wanted
       emitKiImplication implic
  | otherwise
  = return ()
  where
    skol_info_anon = getSkolemInfo skol_info

buildKvImplication
  :: SkolemInfoAnon
  -> [TcKiVar]
  -> TcLevel
  -> WantedKiConstraints
  -> TcM KiImplication
buildKvImplication skol_info skol_kvs tclvl wanted
  = assertPpr (all (isSkolemVar <||> isTcVarVar) skol_kvs) (ppr skol_kvs) $ do
  ki_co_binds <- newTcKiCoBinds
  implic <- newImplication
  let implic' = implic { kic_tclvl = tclvl
                       , kic_skols = skol_kvs
                       , kic_given_kicos = NoGivenKiCos
                       , kic_wanted = wanted
                       , kic_binds = ki_co_binds
                       , kic_info = skol_info }
  checkKiImplicationInvariants implic'
  return implic'

emitResidualTvConstraint
  :: SkolemInfo
  -> [TcTyVar AnyKiVar]
  -> TcLevel
  -> WantedTyConstraints
  -> TcM ()
emitResidualTvConstraint skol_info skol_tvs tclvl wanted
  | not (isEmptyWC wanted)
    || checkTelescopeSkol skol_info_anon
  = do implic <- buildTvImplication skol_info_anon skol_tvs tclvl wanted
       emitTyImplication implic
  | otherwise
  = return ()
  where
    skol_info_anon = getSkolemInfo skol_info

buildTvImplication
  :: SkolemInfoAnon
  -> [TcTyVar AnyKiVar]
  -> TcLevel
  -> WantedTyConstraints
  -> TcM TyImplication
buildTvImplication skol_info skol_vs tclvl wanted
  = assertPpr (all (isSkolemVar <||> isTcVarVar) skol_vs) (ppr skol_vs) $ do
      traceTc "buildTvImplication ******************************"
        $ vcat [ ppr skol_vs, ppr skol_info, ppr wanted ]
      co_binds <- newTcTyCoBinds
      implic <- newImplication
      let implic' = implic { tic_tclvl = tclvl
                           , tic_skols = [] -- skol_vs
                           , tic_given_eqs = NoGivenTyEqs
                           , tic_wanted = wanted
                           , tic_binds = co_binds
                           , tic_info = skol_info }
      checkTyImplicationInvariants implic'
      return implic'

implicationNeeded :: SkolemInfoAnon -> [AnyTyVar AnyKiVar] -> TcM Bool
implicationNeeded skol_info skol_tvs
  | null skol_tvs
  , not (alwaysBuildImplication skol_info)
  = do tc_lvl <- getTcLevel
       if not (isTopTcLevel tc_lvl)
         then return False
         else do dflags <- getDynFlags
                 return $ gopt Opt_DeferTypeErrors dflags
                       || gopt Opt_DeferTypedHoles dflags
                       || gopt Opt_DeferOutOfScopeVariables dflags
  | otherwise
  = return True

kiImplicationNeeded :: SkolemInfoAnon -> [AnyKiVar] -> [KiCoVar kv] -> TcM Bool
kiImplicationNeeded skol_info skol_kvs given
  | null skol_kvs
  , null given
  , not (alwaysBuildImplication skol_info)
  = do tc_lvl <- getTcLevel
       if not (isTopTcLevel tc_lvl)
         then return False
         else do dflags <- getDynFlags
                 return $ gopt Opt_DeferTypeErrors dflags
                       || gopt Opt_DeferTypedHoles dflags
                       || gopt Opt_DeferOutOfScopeVariables dflags
  | otherwise
  = return True

alwaysBuildImplication :: SkolemInfoAnon -> Bool
alwaysBuildImplication _ = False

buildTyKiImplicationFor
  :: TcLevel
  -> SkolemInfoAnon
  -> [AnyKiVar]
  -> [AnyTyVar AnyKiVar]
  -> [KiCoVar AnyKiVar]
  -> WantedTyConstraints
  -> TcM (Bag KiImplication, Bag TyImplication)
buildTyKiImplicationFor tclvl skol_info skol_kvs skol_tvs given wanted
  | isEmptyWC wanted && null given
  = return (emptyBag, emptyBag)
  | Just tc_skol_kvs <- traverse toTcKiVar_maybe skol_kvs
  , Just tc_skol_tvs <- traverse toTcTyVar_maybe skol_tvs
  = assertPpr (all (isSkolemVar <||> isTcVarVar) tc_skol_kvs) (ppr tc_skol_kvs) $
    assertPpr (all (isSkolemVar <||> isTcVarVar) tc_skol_tvs) (ppr tc_skol_tvs) $
    do kco_binds_var <- newTcKiCoBinds
       tco_binds_var <- newTcTyCoBinds
       kiImplic <- newImplication
       tyImplic <- newImplication
       let (kiWanted, tyWanted) = case wanted of
                                    WTC s t k -> (k, WTC s t emptyWC)
           kiImplic' = kiImplic { kic_tclvl = tclvl
                                , kic_skols = tc_skol_kvs
                                , kic_given = given
                                , kic_wanted = kiWanted
                                , kic_binds = kco_binds_var
                                , kic_info = skol_info }
           tyImplic' = tyImplic { tic_tclvl = tclvl
                                , tic_skols = tc_skol_tvs
                                , tic_given = []
                                , tic_wanted = tyWanted
                                , tic_binds = tco_binds_var
                                , tic_info = skol_info }
       checkKiImplicationInvariants kiImplic'
       checkTyImplicationInvariants tyImplic'

       return (unitBag kiImplic', unitBag tyImplic')

  | otherwise
  = pprPanic "buildTyKiImplicationFor" (ppr skol_kvs $$ ppr skol_tvs)

buildKiImplicationFor
  :: TcLevel
  -> SkolemInfoAnon
  -> [AnyKiVar]
  -> [KiCoVar AnyKiVar]
  -> WantedKiConstraints
  -> TcM (Bag KiImplication)
buildKiImplicationFor tclvl skol_info skol_kvs given wanted
  | isEmptyWC wanted && null given
  = return emptyBag
  | Just tc_skol_kvs <- traverse toTcKiVar_maybe skol_kvs
  = assertPpr (all (isSkolemVar <||> isTcVarVar) tc_skol_kvs) (ppr tc_skol_kvs) $
    do co_binds_var <- newTcKiCoBinds
       implic <- newImplication
       let implic' = implic { kic_tclvl = tclvl
                            , kic_skols = tc_skol_kvs
                            , kic_given = given
                            , kic_wanted = wanted
                            , kic_binds = co_binds_var
                            , kic_info = skol_info }
       checkKiImplicationInvariants implic'
       return (unitBag implic')
  | otherwise
  = pprPanic "buildKiImplicationFor" (ppr skol_kvs)

buildTyImplicationFor
  :: TcLevel
  -> SkolemInfoAnon
  -> [AnyTyVar AnyKiVar]
  -> WantedTyConstraints
  -> TcM (Bag TyImplication)
buildTyImplicationFor tclvl skol_info skol_tvs wanted
  | isEmptyWC wanted
  = return emptyBag
  | Just tc_skol_tvs <- traverse toTcTyVar_maybe skol_tvs
  = do binds_var <- newTcTyCoBinds
       implic <- newImplication
       let implic' = implic { tic_tclvl = tclvl
                            , tic_skols = tc_skol_tvs
                            , tic_given = []
                            , tic_wanted = wanted
                            , tic_binds = binds_var
                            , tic_info = skol_info }
       checkTyImplicationInvariants implic'
       return (unitBag implic')
  | otherwise
  = pprPanic "buildTyImplicationFor" (ppr skol_tvs)

matchExpectedFunTys
  :: forall a
   . ExpectedFunTyOrigin
  -> UserTypeCtxt
  -> VisArity
  -> ExpSigmaType
  -> ([ExpPatType] -> ExpRhoType -> TcM a)
  -> TcM (AnyCsWrapper, a)
matchExpectedFunTys herald _ arity (Infer inf_res) thing_inside = do
  (arg_tys, fun_kis) <- unzip <$> mapM new_infer_arg_ty_ki [1..arity]
  res_ty <- newInferExpType
  result <- thing_inside (map ExpFunPatTy arg_tys) res_ty
  arg_tys <- mapM readExpType arg_tys
  res_ty <- readExpType res_ty
  co <- fillInferResult (mkFunTys arg_tys fun_kis res_ty) inf_res
  return (mkWpCast co, result)

matchExpectedFunTys herald ctx arity (Check top_ty) thing_inside
  = check arity [] top_ty
  where
    check :: VisArity -> [ExpPatType] -> AnySigmaType -> TcM (AnyCsWrapper, a)
    -- Skolemize vis/invis quantifiers
    check n_req rev_pat_tys ty
      | isSigmaTy ty
        || (n_req > 0 && isForAllTy ty)
      = do rec { (n_req', wrap_gen, tv_nms, tcbndrs, inner_ty)
                   <- skolemizeRequired skol_info n_req ty
               ; let sig_skol = SigSkol ctx top_ty (tv_nms `zip` skol_tvs)
                     skol_tvs = toAnyTyVar <$> binderVars tcbndrs
                     bndrs = (mapVarBinder toAnyTyVar) <$> tcbndrs
               ; skol_info <- mkSkolemInfo sig_skol }
           (wrap_res, result) <- checkTyConstraints (getSkolemInfo skol_info) skol_tvs
                                 $ check n_req'
                                         (reverse (map ExpForAllPatTy bndrs) ++ rev_pat_tys)
                                         inner_ty
           assertPpr (not (null bndrs)) (ppr ty)
             $ return (wrap_gen <.> wrap_res, result)
    -- Base case
    check n_req rev_pat_tys rho_ty
      | n_req == 0
      = do let pat_tys = reverse rev_pat_tys
           res <- thing_inside pat_tys (mkCheckExpType rho_ty)
           return (idCsWrapper, res)
    -- Function types
    check n_req rev_pat_tys (FunTy { ft_kind = ki, ft_arg = arg_ty, ft_res = res_ty }) = do
      let arg_pos = arity - n_req + 1
      (wrap_res, result) <- check (n_req - 1)
                                  (mkCheckExpFunPatTy arg_ty : rev_pat_tys)
                                  res_ty
      let fun_wrap = mkWpFun wrap_res ki arg_ty
      return (fun_wrap, result)
    -- Type variables
    check n_req rev_pat_tys ty@(TyVarTy tv)
      | Just mtv <- toTcTyVar_maybe tv
      = do cts <- readMetaTyVar mtv
           case cts of
             Indirect ty' -> check n_req rev_pat_tys ty'
             Flexi -> defer n_req rev_pat_tys ty
    -- coreView
    check n_req rev_pat_tys ty
      | Just ty' <- coreView ty = check n_req rev_pat_tys ty'

    check n_req rev_pat_tys res_ty
      = addErrCtxtM (mkFunTysMsg herald (arity, top_ty))
        $ defer n_req rev_pat_tys res_ty

    defer :: VisArity -> [ExpPatType] -> AnyRhoType -> TcM (AnyCsWrapper, a)
    defer n_req rev_pat_tys fun_ty = do
      (more_arg_tys, more_fun_kis)
        <- unzip <$> mapM new_check_arg_ty_ki [arity - n_req + 1 .. arity]
      let all_pats = reverse rev_pat_tys ++ map mkCheckExpFunPatTy more_arg_tys
      res_ty <- asAnyTyKi <$> newOpenFlexiTyVarTy
      result <- thing_inside all_pats (mkCheckExpType res_ty)

      co <- unifyType Nothing (mkFunTys more_arg_tys more_fun_kis res_ty) fun_ty
      return (mkWpCast co, result)

new_infer_arg_ty_ki :: Int -> TcM (ExpSigmaType, AnyMonoKind)
new_infer_arg_ty_ki _ = do
  ki <- asAnyKi <$> newFlexiKiVarKi
  inf_hole <- newInferExpType
  return (inf_hole, ki)

new_check_arg_ty_ki :: Int -> TcM (AnyType, AnyMonoKind)
new_check_arg_ty_ki _ = do
  fun_ki <- asAnyKi <$> newFlexiKiVarKi
  arg_ty <- asAnyTyKi <$> newOpenFlexiTyVarTy
  return (arg_ty, fun_ki)

mkFunTysMsg
  :: ExpectedFunTyOrigin -> (VisArity, AnyType) -> AnyTidyEnv -> ZonkM (AnyTidyEnv, SDoc)
mkFunTysMsg herald (n_vis_args_in_call, fun_ty) env = do
  (env', fun_ty) <- zonkTidyTcType env fun_ty
  let (pi_ty_bndrs, _) = splitPiTys fun_ty
      n_fun_args = count isVisiblePiTyBinder pi_ty_bndrs
      msg | n_vis_args_in_call <= n_fun_args
          = text "In the result of a function call"
          | otherwise
          = hang (full_herald <> comma)
            2 (sep [ text "but its type" <+> quotes (pprSigmaType fun_ty)
                   , if n_fun_args == 0 then text "has none"
                     else text "has only" <+> speakN n_fun_args ])
  return (env', msg)
  where
    full_herald = pprExpectedFunTyHerald herald
                  <+> speakNOf n_vis_args_in_call (text "visible argument")

{- *********************************************************************
*                                                                      *
                fillInferResult
*                                                                      *
********************************************************************* -}

fillInferResult :: AnyType -> InferResult -> TcM AnyTypeCoercion
fillInferResult act_res_ty (IR { ir_uniq = u, ir_lvl = res_lvl, ir_ref = ref }) = do
  mb_exp_res_ty <- readTcRef ref
  case mb_exp_res_ty of
    Just exp_res_ty -> do
      traceTc "Joining inferred ExpType"
        $ ppr u <> colon <+> ppr act_res_ty <+> char '~' <+> ppr exp_res_ty
      cur_lvl <- getTcLevel
      unless (cur_lvl `sameDepthAs` res_lvl)
        $ ensureMonoType act_res_ty
      unifyType Nothing act_res_ty exp_res_ty

    Nothing -> do
      traceTc "Filling inferred ExpType"
        $ ppr u <+> text ":=" <+> ppr act_res_ty
      (prom_co, act_res_ty) <- promoteTcType res_lvl act_res_ty
      writeTcRef ref $ Just act_res_ty
      return prom_co

{- *********************************************************************
*                                                                      *
                Subsumption checking
*                                                                      *
********************************************************************* -}

tcSubTypePat :: CtOrigin -> UserTypeCtxt -> ExpSigmaType -> AnySigmaType -> TcM AnyCsWrapper
tcSubTypePat inst_orig ctxt (Check ty_actual) ty_expected
  = tc_sub_type unifyTypeET inst_orig ctxt ty_actual ty_expected
tcSubTypePat _ _ (Infer _) _ = panic "tcSubTypePat infer"

tcSubTypeSigma
  :: CtOrigin
  -> UserTypeCtxt
  -> AnySigmaType
  -> AnySigmaType
  -> TcM AnyCsWrapper
tcSubTypeSigma orig ctxt ty_actual ty_expected
  = tc_sub_type (unifyType Nothing) orig ctxt ty_actual ty_expected

tc_sub_type
  :: (AnyType -> AnyType -> TcM AnyTypeCoercion)
  -> CtOrigin
  -> UserTypeCtxt
  -> AnySigmaType
  -> AnySigmaType
  -> TcM AnyCsWrapper
tc_sub_type unify inst_orig ctxt ty_actual ty_expected
  | definitely_poly ty_expected
  , isRhoTy ty_actual
  = do traceTc "tc_sub_type (drop to equality)"
         $ vcat [ text "ty_actual =" <+> ppr ty_actual
                , text "ty_expected =" <+> ppr ty_expected ]
       mkWpCast <$> unify ty_actual ty_expected

  | otherwise
  = do traceTc "tc_sub_type (general case)"
         $ vcat [ text "ty_actual =" <+> ppr ty_actual
                , text "ty_expected =" <+> ppr ty_expected ]
       (sk_wrap, inner_wrap) <- tcSkolemize ctxt ty_expected $ \sk_rho ->
         tc_sub_type_shallow unify inst_orig ty_actual sk_rho
       return (sk_wrap <.> inner_wrap)

tc_sub_type_shallow
  :: (AnyType -> AnyType -> TcM AnyTypeCoercion)
  -> CtOrigin
  -> AnySigmaType
  -> AnyRhoType
  -> TcM AnyCsWrapper
tc_sub_type_shallow unify inst_orig ty_actual sk_rho = do
  (wrap, rho_a) <- topInstantiate inst_orig ty_actual
  cow <- unify rho_a sk_rho
  return (mkWpCast cow <.> wrap)

definitely_poly :: AnyType -> Bool
definitely_poly ty
  | (kvs, tvs, tau) <- tcSplitSigma ty
  , (tv:_) <- tvs
  , tv `isInjectiveInType` tau
  = True
  | otherwise
  = False

tcSubMult :: CtOrigin -> BuiltInKi -> AnyKind -> TcM AnyCsWrapper
tcSubMult origin w_actual w_expected
  = case snd $ splitInvisFunKis $ snd $ splitForAllKiVars w_expected of
      FunKi {} -> panic "tcSubMult" (ppr origin $$ ppr w_expected)
      KiPredApp {} -> panic "tcSubMult" (ppr origin $$ ppr w_expected)
      w_expected
        | submult w_actual w_expected
          -> return idCsWrapper
        | otherwise
          -> do kco <- panic "unifyKindAndEmit origin GTEQKi w_actual w_expected"
                if isReflKiCo kco
                  then return idCsWrapper
                  else return $ WpMultCoercion kco

{- *********************************************************************
*                                                                      *
                Type Unification
*                                                                      *
********************************************************************* -}

unifyExprType :: CsExpr Rn -> AnyType -> AnyType -> TcM AnyTypeCoercion
unifyExprType rn_expr ty1 ty2
  = unifyType (Just (CsExprRnThing rn_expr)) ty1 ty2

unifyType :: Maybe TypedThing -> AnyTauType -> AnyTauType -> TcM AnyTypeCoercion
unifyType thing ty1 ty2 = unifyTypeAndEmit origin ty1 ty2
  where
    origin = TypeEqOrigin { uo_actual = ty1
                          , uo_expected = ty2
                          , uo_thing = thing
                          , uo_visible = True }

unifyInvisibleType :: AnyTauType -> AnyTauType -> TcM AnyTypeCoercion
unifyInvisibleType ty1 ty2 = unifyTypeAndEmit origin ty1 ty2
  where
    origin = TypeEqOrigin { uo_actual = ty1
                          , uo_expected = ty2
                          , uo_thing = Nothing
                          , uo_visible = False }

unifyTypeET :: AnyTauType -> AnyTauType -> TcM AnyTypeCoercion
unifyTypeET ty1 ty2 = unifyTypeAndEmit origin ty1 ty2
  where
    origin = TypeEqOrigin { uo_actual = ty2
                          , uo_expected = ty1
                          , uo_thing = Nothing
                          , uo_visible = True }

unifyTypeAndEmit :: CtOrigin -> AnyType -> AnyType -> TcM AnyTypeCoercion
unifyTypeAndEmit orig ty1 ty2 = do
  ty_ref <- newTcRef emptyBag
  ki_ref <- newTcRef emptyBag
  loc <- getCtLocM orig (Just TypeLevel)
  let env = UE { u_loc = loc
               , u_ki_rewriters = emptyKiRewriterSet
               , u_ty_rewriters = emptyTyRewriterSet
               , u_ty_defer = ty_ref
               , u_ki_defer = ki_ref
               , u_ki_unified = Nothing
               , u_ty_unified = Nothing }
  co <- uType env ty1 ty2
  ty_cts <- readTcRef ty_ref
  unless (null ty_cts) (emitTySimples ty_cts)
  ki_cts <- readTcRef ki_ref
  unless (null ki_cts) (emitKiSimples ki_cts)
  return co

{- *********************************************************************
*                                                                      *
                Kind Unification
*                                                                      *
********************************************************************* -}

unifyKind :: Maybe KindedThing -> KiPredCon -> AnyMonoKind -> AnyMonoKind -> TcM AnyKindCoercion
unifyKind thing kc ki1 ki2 = unifyKindAndEmit origin kc ki1 ki2
  where
    origin = KindCoOrigin { kco_actual = ki1
                          , kco_expected = ki2
                          , kco_pred = kc
                          , kco_thing = thing
                          , kco_visible = True }

unifyKindAndEmit :: CtOrigin -> KiPredCon -> AnyMonoKind -> AnyMonoKind -> TcM AnyKindCoercion
unifyKindAndEmit orig kc ki1 ki2 = do
  ki_ref <- newTcRef emptyBag
  loc <- getCtLocM orig (Just KindLevel)
  let env = UE { u_loc = loc
               , u_ki_rewriters = emptyKiRewriterSet
               , u_ki_defer = ki_ref
               , u_ki_unified = Nothing
               , u_ty_rewriters = panic "unifyKindAndEmit u_ty_rewriters"
               , u_ty_defer = panic "unifyKindAndEmit u_ty_defer"
               , u_ty_unified = panic "unifyKindAndEmit u_ty_unified" }
  co <- uKind env kc ki1 ki2
  ki_cts <- readTcRef ki_ref
  unless (null ki_cts) (emitKiSimples ki_cts)
  return co

{- *********************************************************************
*                                                                      *
                uType
*                                                                      *
********************************************************************* -}

data UnifyEnv = UE
  { u_loc :: CtLoc
  , u_ty_rewriters :: TyRewriterSet
  , u_ki_rewriters :: KiRewriterSet
  , u_ty_defer :: TcRef TyCts
  , u_ki_defer :: TcRef KiCts
  , u_ty_unified :: Maybe (TcRef [TcTyVar AnyKiVar])
  , u_ki_unified :: Maybe (TcRef [TcKiVar])
  }

updUEnvLoc :: UnifyEnv -> (CtLoc -> CtLoc) -> UnifyEnv
updUEnvLoc uenv@(UE { u_loc = loc }) upd = uenv { u_loc = upd loc }

mkKindEnv :: UnifyEnv -> AnyType -> AnyType -> UnifyEnv
mkKindEnv env@(UE { u_loc = ctloc }) ty1 ty2
  = env { u_loc = mkKindEqLoc ty1 ty2 ctloc }

uType_defer :: UnifyEnv -> AnyType -> AnyType -> TcM AnyTypeCoercion
uType_defer (UE { u_loc = loc, u_ty_defer = ref, u_ty_rewriters = rewriters }) ty1 ty2 = do
  let pred_ty = mkTyEqPred ty1 ty2
  hole <- newTyCoercionHole pred_ty
  let ct = mkNonCanonicalTy
           $ CtTyWanted { cttev_pred = pred_ty
                        , cttev_dest = hole
                        , cttev_loc = loc
                        , cttev_rewriters = rewriters }
      co = TyHoleCo hole
  updTcRef ref (`snocBag` ct)

  whenDOptM Opt_D_dump_tc_trace $ do
    ctxt <- getErrCtxt
    doc <- mkErrInfo emptyTidyEnv ctxt
    traceTc "uType_defer"
      $ vcat [ debugPprType ty1, debugPprType ty2, doc ]
    traceTc "uType_defer2" (ppr co)

  return co

uType :: UnifyEnv -> AnyType -> AnyType -> TcM AnyTypeCoercion
uType env orig_ty1 orig_ty2 = do
  tclvl <- getTcLevel
  traceTc "u_tys"
    $ vcat [ text "tclvl" <+> ppr tclvl
           , sep [ ppr orig_ty1, text "~", ppr orig_ty2 ] ]

  co <- go orig_ty1 orig_ty2
  if isReflTyCo co
    then traceTc "u_tys yields no coercion:" empty
    else traceTc "u_tys yields coercion:" (ppr co)
  return co

  where
    go :: AnyType -> AnyType -> TcM AnyTypeCoercion

    go (CastTy t1 kco1) t2 = do
      co_tys <- uType env t1 t2
      return $ mkCoherenceLeftCo t1 kco1 co_tys

    go t1 (CastTy t2 kco2) = do
      co_tys <- uType env t1 t2
      return $ mkCoherenceRightCo t2 kco2 co_tys

    go (TyVarTy tv1) ty2 = do
      lookup_res <- handleAnyTv (const $ return Nothing) isFilledMetaTyVar_maybe tv1
      case lookup_res of
        Just ty1 -> do traceTc "found filled tyvar" (ppr tv1 <+> text ":->" <+> ppr ty1)
                       uType env ty1 orig_ty2
        Nothing -> uUnfilledTyVar env NotSwapped tv1 ty2

    go ty1 (TyVarTy tv2) = do
      lookup_res <- handleAnyTv (const $ return Nothing) isFilledMetaTyVar_maybe tv2
      case lookup_res of
        Just ty2 -> do traceTc "found filled tyvar" (ppr tv2 <+> text ":->" <+> ppr ty2)
                       uType env orig_ty1 ty2
        Nothing -> uUnfilledTyVar env IsSwapped tv2 ty1

    go ty1@(TyConApp tc1 []) ty2@(TyConApp tc2 [])
      | tc1 == tc2
      = return $ mkReflTyCo ty1

    go ty1 ty2
      | Just ty1' <- coreView ty1 = go ty1' ty2
      | Just ty2' <- coreView ty2 = go ty1 ty2'

    go ty1@(FunTy { ft_kind = k1, ft_arg = arg1, ft_res = res1 })
       ty2@(FunTy { ft_kind = k2, ft_arg = arg2, ft_res = res2 })
      = do kco <- uKind (mkKindEnv env ty1 ty2) EQKi k1 k2
           co_l <- uType env arg1 arg2
           co_r <- uType env res1 res2
           return $ mkTyFunCo kco co_l co_r

    go ty1@(TyConApp tc1 tys1) ty2@(TyConApp tc2 tys2)
      | tc1 == tc2
      , equalLength tys1 tys2
      , isInjectiveTyCon tc1
      = assertPpr (isGenerativeTyCon tc1) (ppr tc1) $ do
          traceTc "go-tycon" (ppr tc1 $$ ppr tys1 $$ ppr tys2)
          cos <- zipWith3M u_tc_arg (tyConVisibilities tc1) tys1 tys2
          return $ mkTyConAppCo tc1 cos

    go ty1@(AppTy s1 t1) ty2@(AppTy s2 t2)
      = go_app (isNextArgVisible s1) ty1 s1 t1 ty2 s2 t2

    go ty1@(AppTy s1 t1) ty2@(TyConApp tc2 ts2)
      | Just (ts2', t2') <- snocView ts2
      = assert (not (tyConMustBeSaturated tc2))
        $ go_app (isNextTyConArgVisible tc2 ts2') ty1 s1 t1 ty2 (TyConApp tc2 ts2') t2'

    go ty1@(TyConApp tc1 ts1) ty2@(AppTy s2 t2)
      | Just (ts1', t1') <- snocView ts1
      = assert (not (tyConMustBeSaturated tc1))
        $ go_app (isNextTyConArgVisible tc1 ts1') ty1 (TyConApp tc1 ts1') t1' ty2 s2 t2

    go ty1@(KindCoercion kco1) ty2@(KindCoercion kco2) = do
      kco <- uKind (mkKindEnv env ty1 ty2) EQKi (kiCoercionKind kco1) (kiCoercionKind kco2)
      return $ liftKCo kco

    go ty1@(Embed ki1) ty2@(Embed ki2) = do
      kco <- uKind (mkKindEnv env ty1 ty2) EQKi ki1 ki2
      return $ liftKCo kco

    go ty1 ty2 = defer ty1 ty2

    defer ty1 ty2
      | ty1 `tcEqType` ty2 = return (mkReflTyCo ty1)
      | otherwise = uType_defer env orig_ty1 orig_ty2

    u_tc_arg is_vis ty1 ty2 = do
      traceTc "u_tc_arg" (ppr ty1 $$ ppr ty2)
      uType env_arg ty1 ty2
      where
        env_arg = env { u_loc = adjustCtLoc is_vis False (u_loc env) }                      

    go_app vis ty1 s1 t1 ty2 s2 t2 = panic "go_app"

{- *********************************************************************
*                                                                      *
                uKind
*                                                                      *
********************************************************************* -}

uKind_defer :: UnifyEnv -> KiPredCon -> AnyMonoKind -> AnyMonoKind -> TcM AnyKindCoercion
uKind_defer (UE { u_loc = loc, u_ki_defer = ref, u_ki_rewriters = rewriters }) kc ki1 ki2 = do
  let pred_ki = mkKiCoPred kc ki1 ki2
  hole <- newKiCoercionHole pred_ki
  let ct = mkNonCanonicalKi
           $ CtKiWanted { ctkev_pred = pred_ki
                      , ctkev_dest = hole
                      , ctkev_loc = loc
                      , ctkev_rewriters = rewriters }
      co = HoleCo hole
  updTcRef ref (`snocBag` ct)
  whenDOptM Opt_D_dump_tc_trace $ do
    ctxt <- getErrCtxt
    doc <- mkErrInfo emptyTidyEnv ctxt
    traceTc "uKind_defer"
      $ vcat [ ppr kc, debugPprMonoKind ki1, debugPprMonoKind ki2, doc ]
    traceTc "uKind_defer2" (ppr co)

  return co

uKind :: UnifyEnv -> KiPredCon -> AnyMonoKind -> AnyMonoKind -> TcM AnyKindCoercion
uKind env kc orig_ki1 orig_ki2 = do
  tclvl <- getTcLevel
  traceTc "u_kis"
    $ vcat [ text "tclvl" <+> ppr tclvl
           , sep [ ppr orig_ki1, ppr kc, ppr orig_ki2 ] ]
  co <- go orig_ki1 orig_ki2
  if isReflKiCo co
    then traceTc "u_kis yields no coercion" empty
    else traceTc "u_kis yields coercion:" (ppr co)
  return co
  where   
    go :: AnyMonoKind -> AnyMonoKind -> TcM AnyKindCoercion

    go (KiVarKi kv1) ki2 = do
      lookup_res <- handleAnyKv (const $ return Nothing) isFilledMetaKiVar_maybe kv1
      case lookup_res of
        Just ki1 -> do traceTc "found filled kivar" (ppr kv1 <+> text ":->" <+> ppr ki1)
                       uKind env kc ki1 orig_ki2
        Nothing -> uUnfilledKiVar env NotSwapped kc kv1 ki2

    go ki1 (KiVarKi kv2) = do
      lookup_res <- handleAnyKv (const $ return Nothing) isFilledMetaKiVar_maybe kv2
      case lookup_res of
        Just ki2 -> do traceTc "found filled kivar" (ppr kv2 <+> text ":->" <+> ppr ki2)
                       uKind env kc orig_ki1 ki2
        Nothing -> uUnfilledKiVar env IsSwapped kc kv2 ki1

    go ki1@(BIKi kc1) (BIKi kc2)
      | kc1 == kc2
      , EQKi <- kc
      = return $ mkReflKiCo ki1
      | kc1 == kc2
      , LTEQKi <- kc
      = return $ LiftEq $ mkReflKiCo ki1
      | kc1 < kc2
      , LTKi <- kc
      = case (kc1, kc2) of
          (UKd, AKd) -> return BI_U_A
          (AKd, LKd) -> return BI_A_L
          (UKd, LKd) -> return $ TransCo BI_U_A BI_A_L
          _ -> panic "unreachable"
      | kc1 < kc2
      , LTEQKi <- kc
      = case (kc1, kc2) of
          (UKd, AKd) -> return $ LiftLT BI_U_A
          (AKd, LKd) -> return $ LiftLT BI_A_L
          (UKd, LKd) -> return $ LiftLT $ TransCo BI_U_A BI_A_L
          _ -> panic "unreachable"

    go k1@(KiPredApp p1 ka1 kb1) k2@(KiPredApp p2 ka2 kb2) 
      | p1 == p2
      , EQKi <- kc -- maybe this should be an assert
      = do traceTc "go-kipred" (ppr k1 $$ ppr k2)
           coa <- u_kc_arg ka1 ka2 
           cob <- u_kc_arg kb1 kb2
           massertPpr (isReflKiCo coa && isReflKiCo cob)
             $ vcat [ text "uKind/go_kipred has non-reflexive argument coercion"
                    , ppr coa, ppr cob ]
           return $ mkReflKiCo k1

    go (FunKi FKF_K_K arg1 res1) (FunKi FKF_K_K arg2 res2) = do
      massertPpr (kc == EQKi)
        $ vcat [ text "uKind/go-funki has non-EQKi relation"
               , ppr kc, ppr orig_ki1, ppr orig_ki2 ]
      co_l <- uKind env kc arg1 arg2
      co_r <- uKind env kc res1 res2
      return $ mkFunKiCo FKF_K_K co_l co_r 

    go ki1 ki2 = defer kc ki1 ki2

    ------------------
    defer kc ki1 ki2
      | ki1 `tcEqMonoKind` ki2
      , EQKi <- kc
      = return $ mkReflKiCo ki1
      | ki1 `tcEqMonoKind` ki2
      , LTEQKi <- kc
      = return $ LiftEq $ mkReflKiCo ki1
      | otherwise = uKind_defer env kc orig_ki1 orig_ki2

    ------------------
    u_kc_arg ki1 ki2 = do
      traceTc "u_kc_arg" (ppr ki1 $$ ppr ki2)
      uKind env_arg kc ki1 ki2
      where
        env_arg = env { u_loc = adjustCtLoc False True (u_loc env) }

{- *********************************************************************
*                                                                      *
                 uUnfilledTyVar and friends
*                                                                      *
********************************************************************* -}

uUnfilledTyVar :: UnifyEnv -> SwapFlag -> AnyTyVar AnyKiVar -> AnyTauType -> TcM AnyTypeCoercion
uUnfilledTyVar env swapped tv1 ty2 = do
  ty2 <- liftZonkM $ zonkTcType ty2
  uUnfilledTyVar1 env swapped tv1 ty2

uUnfilledTyVar1 :: UnifyEnv -> SwapFlag -> AnyTyVar AnyKiVar -> AnyTauType -> TcM AnyTypeCoercion
uUnfilledTyVar1 env swapped tv1 ty2
  | Just tv2 <- getTyVar_maybe ty2
  = go tv2
  | otherwise
  = uUnfilledTyVar2 env swapped tv1 ty2
  where
    go tv2 | tv1 == tv2
           = return (mkReflTyCo (mkTyVarTy tv1))
           | swapOverTyVars False tv1 tv2
           = do tv1 <- liftZonkM $ zonkTyVarKind tv1
                uUnfilledTyVar2 env (flipSwap swapped) tv2 (mkTyVarTy tv1)
           | otherwise
           = uUnfilledTyVar2 env swapped tv1 ty2

uUnfilledTyVar2 :: UnifyEnv -> SwapFlag -> AnyTyVar AnyKiVar -> AnyTauType -> TcM AnyTypeCoercion
uUnfilledTyVar2 env@(UE { u_ty_defer = def_eq_ref }) swapped tv1 ty2 = do
  cur_lvl <- getTcLevel
  case toTcTyVar_maybe tv1 of
    Just tctv1
      | touchabilityAndShapeTestType cur_lvl tctv1 ty2
      , simpleUnifyCheckType UC_OnTheFly tctv1 ty2
        ->  do def_eqs <- readTcRef def_eq_ref
               kco <- uKind (mkKindEnv env ty1 ty2) EQKi (typeMonoKind ty2) (varKind tctv1)
               traceTc "uUnfilledTyVar2 ok"
                 $ vcat [ ppr tctv1 <+> colon <+> ppr (varKind tctv1)
                        , ppr ty2 <+> colon <+> ppr (typeMonoKind ty2)
                        , ppr (isReflKiCo kco)
                        , ppr kco ]
               if isReflKiCo kco
                 then do liftZonkM $ writeMetaTyVar tctv1 ty2
                         case u_ty_unified env of
                           Nothing -> return ()
                           Just uref -> updTcRef uref (tctv1 :)
                         return (mkReflTyCo ty2)
                 else do writeTcRef def_eq_ref def_eqs
                         defer
    _ -> not_ok_so_defer cur_lvl
  where
    ty1 = mkTyVarTy tv1
    defer = unSwap swapped (uType_defer env) ty1 ty2

    not_ok_so_defer cur_lvl = do
      traceTc "uUnfilledTyVar2 not ok"
        $ vcat [ text "tv1:" <+> ppr tv1
               , text "ty2:" <+> ppr ty2 ]
      defer

swapOverTyVars :: Bool -> AnyTyVar AnyKiVar -> AnyTyVar AnyKiVar -> Bool
swapOverTyVars is_given tv1 tv2
  | not is_given, pri1 == 0, pri2 > 0 = True
  | not is_given, pri2 == 0, pri2 > 0 = False
  | lvl1 `strictlyDeeperThan` lvl2 = False
  | lvl2 `strictlyDeeperThan` lvl1 = True
  | pri1 > pri2 = False
  | pri2 > pri1 = True
  | isSystemName tv2_name, not (isSystemName tv1_name) = True
  | otherwise = False
  where
    lvl1 = handleAnyTv (const topTcLevel) varLevel tv1
    lvl2 = handleAnyTv (const topTcLevel) varLevel tv2
    pri1 = lhsTyPriority tv1
    pri2 = lhsTyPriority tv2
    tv1_name = Var.varName tv1
    tv2_name = Var.varName tv2

lhsTyPriority :: AnyTyVar AnyKiVar -> Int
lhsTyPriority = 
  handleAnyTv (const 0) $ \ tv ->
  case tcVarDetails tv of
    SkolemVar {} -> 0
    MetaVar { mv_info = info } -> case info of
                                    VarVar -> 1
                                    TauVar -> 3

{- *********************************************************************
*                                                                      *
                 uUnfilledKiVar and friends
*                                                                      *
********************************************************************* -}

uUnfilledKiVar
  :: UnifyEnv -> SwapFlag -> KiPredCon -> AnyKiVar -> AnyMonoKind -> TcM AnyKindCoercion
uUnfilledKiVar env swapped kc kv1 ki2 = do
  ki2 <- liftZonkM $ zonkTcMonoKind ki2
  uUnfilledKiVar1 env swapped kc kv1 ki2

uUnfilledKiVar1
  :: UnifyEnv -> SwapFlag -> KiPredCon -> AnyKiVar -> AnyMonoKind -> TcM AnyKindCoercion
uUnfilledKiVar1 env swapped kc kv1 ki2
  | Just kv2 <- getKiVar_maybe ki2
  = go kv2
  | otherwise
  = uUnfilledKiVar2 env swapped kc kv1 ki2
  where
    go kv2
      | kv1 == kv2
      , EQKi <- kc
      = return $ mkReflKiCo (mkKiVarKi kv1)
      | kv1 == kv2
      , LTEQKi <- kc
      = return $ LiftEq $ mkReflKiCo (mkKiVarKi kv1)
      | swapOverKiVars False kv1 kv2
      = uUnfilledKiVar2 env (flipSwap swapped) kc kv2 (mkKiVarKi kv1)
      | otherwise
      = uUnfilledKiVar2 env swapped kc kv1 ki2

uUnfilledKiVar2
  :: UnifyEnv -> SwapFlag -> KiPredCon -> AnyKiVar -> AnyMonoKind -> TcM AnyKindCoercion
uUnfilledKiVar2 env swapped kc kv1 ki2 = do
  cur_lvl <- getTcLevel
  case toTcKiVar_maybe kv1 of
    Just tckv1
      | touchabilityAndShapeTestKind cur_lvl tckv1 ki2
      , simpleUnifyCheckKind tckv1 ki2
      , kc == EQKi
        -> do traceTc "uUnfilledKiVar2 ok" $ vcat [ ppr kc, ppr tckv1, ppr ki2 ]
              liftZonkM $ writeMetaKiVar tckv1 ki2
              case u_ki_unified env of
                Nothing -> return ()
                Just uref -> updTcRef uref (tckv1 :)
              return $ case kc of
                         EQKi -> mkReflKiCo ki2
                         _ -> panic "unreachable"

    _ -> not_ok_so_defer
  where
    ki1 = mkKiVarKi kv1
    defer = unSwap swapped (uKind_defer env kc) ki1 ki2
    not_ok_so_defer = do
      traceTc "uUnfilledVar2 not ok" (ppr kv1 $$ ppr ki2)
      defer            

swapOverKiVars :: Bool -> AnyKiVar -> AnyKiVar -> Bool
swapOverKiVars is_given kv1 kv2
  | not is_given, pri1 == 0, pri2 > 0 = True
  | not is_given, pri2 == 0, pri1 > 0 = False

  | lvl1 `strictlyDeeperThan` lvl2 = False
  | lvl2 `strictlyDeeperThan` lvl1 = True

  | pri1 > pri2 = False
  | pri2 > pri1 = True

  | isSystemName kv2_name, not (isSystemName kv1_name) = True

  | otherwise = False
  where
    lvl1 = handleAnyKv (const topTcLevel) varLevel kv1
    lvl2 = handleAnyKv (const topTcLevel) varLevel kv2
    pri1 = lhsKiPriority kv1
    pri2 = lhsKiPriority kv2
    kv1_name = Var.varName kv1
    kv2_name = Var.varName kv2

lhsKiPriority :: AnyKiVar -> Int
lhsKiPriority =
  handleAnyKv (const 0) $ \ kv ->
  case tcVarDetails kv of
    SkolemVar {} -> 0
    MetaVar { mv_info = info } -> case info of
                                    VarVar -> 1
                                    TauVar -> 3

matchExpectedFunKind :: KindedThing -> Arity -> AnyMonoKind -> TcM AnyKindCoercion
matchExpectedFunKind cs_ty n k = go n k
  where
    go :: Arity -> AnyMonoKind -> TcM AnyKindCoercion
    go 0 k = return (mkReflKiCo k)
    go n k@(KiVarKi kvar)
      | Just kvar <- toTcKiVar_maybe kvar
      , isMetaVar kvar
      = do maybe_kind <- readMetaKiVar kvar
           case maybe_kind of
             Indirect fun_kind -> go n fun_kind
             Flexi -> defer n k
    go n (FunKi { fk_f = af, fk_arg = arg, fk_res = res })
      | isVisibleKiFunArg af
      = do co <- go (n-1) res
           return $ mkFunKiCo af (mkReflKiCo arg) co
    go n other = defer n other

    defer n k = do
      arg_kinds <- newMetaKindVars n
      res_kind <- newMetaKindVar
      let new_fun = asAnyKi $ mkVisFunKis arg_kinds res_kind
          origin = KindCoOrigin { kco_actual = k
                                , kco_expected = new_fun
                                , kco_pred = EQKi
                                , kco_thing = Just cs_ty
                                , kco_visible = True
                                }
      unifyKindAndEmit origin EQKi k new_fun

{- *********************************************************************
*                                                                      *
                 Checking alpha ~ ki
              for the on-the-fly unifier
*                                                                      *
********************************************************************* -}

simpleUnifyCheckKind  :: TcKiVar -> AnyMonoKind -> Bool
simpleUnifyCheckKind lhs_kv rhs = go_mono rhs
  where
    lhs_kv_lvl = varLevel lhs_kv

    go_mono (KiVarKi kv)
      | Just tckv <- toTcKiVar_maybe kv
      , lhs_kv == tckv = False
      | handleAnyKv (const topTcLevel) varLevel kv `strictlyDeeperThan` lhs_kv_lvl = False
      | otherwise = True

    go_mono (FunKi { fk_f = af, fk_arg = a, fk_res = r })
      | af == FKF_C_K = False
      | otherwise = go_mono a && go_mono r

    go_mono (BIKi {}) = True

    go_mono (KiPredApp _ k1 k2) = go_mono k1 && go_mono k2

data UnifyCheckCaller
  = UC_OnTheFly
  | UC_QuickLook
  | UC_Solver

simpleUnifyCheckType :: UnifyCheckCaller -> TcTyVar AnyKiVar -> AnyType -> Bool
simpleUnifyCheckType caller lhs_tv rhs = go rhs
  where
    lhs_tv_lvl = varLevel lhs_tv

    forall_ok = case caller of
                  UC_QuickLook -> isQLInstVar lhs_tv
                  _ -> False

    go :: AnyType -> Bool
    go (TyVarTy tv)
      | Just tctv <- toTcTyVar_maybe tv, lhs_tv == tctv = False
      | handleAnyTv (const topTcLevel) varLevel tv `strictlyDeeperThan` lhs_tv_lvl = False
      | otherwise = True

    go (FunTy { ft_arg = a, ft_res = r }) = go a && go r

    go (TyConApp tc tys)
      | not forall_ok, not (isTauTyCon tc) = False
      | otherwise = all go tys

    go (ForAllTy (Bndr tv _) ty)
      | forall_ok, Just tctv <- toTcTyVar_maybe tv = (tctv == lhs_tv || go ty)
      | forall_ok = go ty
      | otherwise = False

    go (AppTy t1 t2) = go t1 && go t2
    go (CastTy ty kco) = panic "simpleUnifyCheckType CastTy" -- probably do need the occFolder
    go (KindCoercion kco) = panic "simpleUnifyCheckType KindCoercion" -- the lhs_tv could be a kcovar?

    go (Embed mki) = go_ki mki
    go other = pprPanic "simpleUnifyCheckType other" (ppr other)

    go_ki (KiVarKi kv)
      | handleAnyKv (const topTcLevel) varLevel kv `strictlyDeeperThan` lhs_tv_lvl = False
      | otherwise = True
    go_ki BIKi{} = True
    go_ki KiPredApp{} = False -- ??
    go_ki FunKi { fk_f = af } = isVisibleKiFunArg af
    
{- *********************************************************************
*                                                                      *
                 Equality invariant checking
*                                                                      *
********************************************************************* -}

-- I don't think I ever use 'Bag a' to add constraints:
-- In GHC I think this only arises from TypeFamilies, so I should be good to remove it
data PuResult a b
  = PuFail CheckTyKiEqResult
  | PuOK (Bag a) b

instance Functor (PuResult a) where
  fmap _ (PuFail prob) = PuFail prob
  fmap f (PuOK cts x) = PuOK cts (f x)

instance Applicative (PuResult a) where
  pure x = PuOK emptyBag x
  PuFail p1 <*> PuFail p2 = PuFail (p1 S.<> p2)
  PuFail p1 <*> PuOK {} = PuFail p1
  PuOK {} <*> PuFail p2 = PuFail p2
  PuOK c1 f <*> PuOK c2 x = PuOK (c1 `unionBags` c2) (f x)

instance (Outputable a, Outputable b) => Outputable (PuResult a b) where
  ppr (PuFail prob) = text "PuFail" <+> (ppr prob)
  ppr (PuOK cts x) = text "PuOk" <> (braces
                     $ vcat [ text "redn:" <+> ppr x
                            , text "cts:" <+> ppr cts ])

okCheckReflTy :: AnyType -> TcM (PuResult a TyReduction)
okCheckReflTy = return . PuOK emptyBag . mkReflRednTy 

okCheckReflKi :: AnyMonoKind -> TcM (PuResult a KiReduction)
okCheckReflKi = return . PuOK emptyBag . mkReflRednKi

failCheckWith :: CheckTyKiEqResult -> TcM (PuResult a b)
failCheckWith p = return $ PuFail p

mapCheck :: (x -> TcM (PuResult a TyReduction)) -> [x] -> TcM (PuResult a TyReductions)
mapCheck f xs = do
  ress <- mapM f xs
  return (unzipRedns <$> sequenceA ress)

data TyEqFlags = TEF
  { tef_foralls :: Bool
  , tef_unifying :: AreUnifying
  , tef_lhs :: CanTyEqLHS
  , tef_occurs :: CheckTyKiEqProblem
  }

data KiEqFlags = KEF
  { kef_foralls :: Bool -- always false: we work only on monokinds (can prob remove)
  , kef_lhs :: CanKiCoLHS
  , kef_unifying :: AreUnifying
  , kef_occurs :: CheckTyKiEqProblem
  }

data AreUnifying
  = Unifying MetaInfo TcLevel LevelCheck
  | NotUnifying

data LevelCheck
  = LC_None
  | LC_Check
  | LC_Promote

instance Outputable KiEqFlags where
  ppr (KEF {..}) = text "KEF" <> (braces
                   $ vcat [ text "kef_lhs =" <+> ppr kef_lhs
                          , text "kef_unifying =" <+> ppr kef_unifying
                          , text "kef_occurs =" <+> ppr kef_occurs ])

instance Outputable AreUnifying where
  ppr NotUnifying = text "NotUnifying"
  ppr (Unifying mi lvl lc) = text "Unifying" <+>
                             (braces $ ppr mi <> comma <+> ppr lvl <> comma <+> ppr lc)

instance Outputable LevelCheck where
  ppr LC_None = text "LC_None"
  ppr LC_Check = text "LC_Check"
  ppr LC_Promote = text "LC_Promote"

checkTyEqRhs :: TyEqFlags -> AnyType -> TcM (PuResult () TyReduction)
checkTyEqRhs flags ty = case ty of
  TyConApp tc tys -> checkTyConApp flags ty tc tys
  TyVarTy tv -> checkTyVar flags tv
  FunTy { ft_kind = ki, ft_arg = a, ft_res = r } -> do
    a_res <- checkTyEqRhs flags a
    r_res <- checkTyEqRhs flags r
    return $ mkFunTyRedn (mkReflRednKi ki) <$> a_res <*> r_res
  AppTy fun arg -> do
    fun_res <- checkTyEqRhs flags fun
    arg_res <- checkTyEqRhs flags arg
    return $ mkAppRedn <$> fun_res <*> arg_res
  CastTy ty kco -> do
    ty_res <- checkTyEqRhs flags ty
    return $ mkCastRedn1 ty kco <$> ty_res
  Embed{} -> okCheckReflTy ty
  KindCoercion{} -> okCheckReflTy ty
  ForAllTy {}
    | tef_foralls flags -> okCheckReflTy ty
    | otherwise -> failCheckWith impredicativeProblem
  _ -> pprPanic "checkTyEqRhs" (ppr ty)

checkTyConApp
  :: TyEqFlags
  -> AnyType -> AnyTyCon -> [AnyType]
  -> TcM (PuResult () TyReduction)
checkTyConApp flags@(TEF { tef_unifying = unifying, tef_foralls = foralls_ok }) tc_app tc tys
  | Just ty' <- rewriterView tc_app
  = checkTyEqRhs flags ty'
  | not (isTauTyCon tc || foralls_ok)
  = failCheckWith impredicativeProblem
  | otherwise
  = recurseIntoTyConApp flags tc tys

recurseIntoTyConApp :: TyEqFlags -> AnyTyCon -> [AnyType] -> TcM (PuResult () TyReduction)
recurseIntoTyConApp flags tc tys = do
  tys_res <- mapCheck (checkTyEqRhs flags) tys
  return $ mkTyConAppRedn tc <$> tys_res

checkTyVar :: TyEqFlags -> AnyTyVar AnyKiVar -> TcM (PuResult a TyReduction)
checkTyVar
  (TEF { tef_lhs = TyVarLHS lhs_tv, tef_unifying = unifying, tef_occurs = occ_prob }) occ_tv
  = check_tv unifying lhs_tv
  where
    lvl_occ = handleAnyTv (const topTcLevel) varLevel occ_tv
    success = okCheckReflTy $ mkTyVarTy occ_tv

    check_tv NotUnifying lhs_tv = simple_occurs_check lhs_tv
    check_tv (Unifying info lvl prom) lhs_tv = do
      mb_done <- handleAnyTv (const $ return Nothing) isFilledMetaTyVar_maybe occ_tv
      case mb_done of
        Just {} -> success
        Nothing -> check_unif info lvl prom lhs_tv

    check_unif lhs_tv_info lhs_tv_lvl prom lhs_tv
      | lvl_occ `strictlyDeeperThan` lhs_tv_lvl
      = case prom of
          LC_None -> pprPanic "check_unif" (ppr lhs_tv $$ ppr occ_tv)
          LC_Check -> failCheckWith (ctkeProblem ctkeSkolemEscape)
          LC_Promote{}
            | Just tc_occ_tv <- toTcTyVar_maybe occ_tv
            , isSkolemVar tc_occ_tv
              -> failCheckWith (ctkeProblem ctkeSkolemEscape)
            | otherwise
              -> promote lhs_tv lhs_tv_info lhs_tv_lvl
      | otherwise
      = simple_occurs_check lhs_tv

    simple_occurs_check lhs_tv
      | lhs_tv == occ_tv
      = failCheckWith (ctkeProblem occ_prob)
      | otherwise
      = success

    promote lhs_tv lhs_tv_info lhs_tv_lvl
      | Just tc_occ_tv <- toTcTyVar_maybe occ_tv
      , MetaVar { mv_info = info_occ, mv_tclvl = lvl_occ } <- tcVarDetails tc_occ_tv
      = do let new_lvl = lhs_tv_lvl `minTcLevel` lvl_occ
           reason <- checkPromoteFreeKiVars lhs_tv_lvl (varsOfMonoKind (varKind occ_tv))

           if ctkerHasNoProblem reason
             then do new_tv_ty <- promote_meta_tyvar info_occ new_lvl tc_occ_tv
                     okCheckReflTy new_tv_ty
             else failCheckWith reason
      | otherwise
      = pprPanic "promote" (ppr occ_tv)

checkPromoteFreeKiVars :: TcLevel -> AnyKiVarSet -> TcM CheckTyKiEqResult
checkPromoteFreeKiVars lhs_tv_lvl vs = do
  oks <- mapM do_one (nonDetEltsUniqSet vs)
  return $ mconcat oks
  where
    do_one v | no_promotion = return ctkeOK
             | Just tc_v <- toTcKiVar_maybe v
             = if not (isMetaVar tc_v) then return $ ctkeProblem ctkeSkolemEscape
               else promote_one tc_v
             | otherwise = pprPanic "checkPromoteFreeKiVars" (ppr v)
      where
        v_lvl = handleAnyKv (const topTcLevel) varLevel v
        no_promotion = not (v_lvl `strictlyDeeperThan` lhs_tv_lvl)

    promote_one kv = do _ <- promote_meta_kivar TauVar lhs_tv_lvl kv
                        return ctkeOK

promote_meta_tyvar :: MetaInfo -> TcLevel -> TcTyVar AnyKiVar -> TcM AnyType
promote_meta_tyvar info dest_lvl occ_tv = do
  mb_filled <- isFilledMetaTyVar_maybe occ_tv
  case mb_filled of
    Just ty -> return ty
    Nothing -> do new_tv <- toAnyTyVar <$> cloneMetaTyVarWithInfo info dest_lvl occ_tv
                  liftZonkM $ writeMetaTyVar occ_tv (mkTyVarTy new_tv)
                  traceTc "promoteTyVar" (ppr occ_tv <+> text "-->" <+> ppr new_tv)
                  return $ mkTyVarTy new_tv

checkKiEqRhs :: KiEqFlags -> AnyMonoKind -> TcM (PuResult () KiReduction)
checkKiEqRhs flags ki = case ki of
  KiPredApp {} -> panic "checkKiEqRhs" --checkKiConApp flags ki kc kis
               -- maybe 'fail impredicative'??
  BIKi {} -> okCheckReflKi ki
  KiVarKi kv -> checkKiVar flags kv
  FunKi { fk_f = af, fk_arg = a, fk_res = r }
    | FKF_C_K <- af
    , not (kef_foralls flags)
    -> failCheckWith impredicativeProblem
    | otherwise
    -> do a_res <- checkKiEqRhs flags a
          r_res <- checkKiEqRhs flags r
          return $ mkFunKiRedn af <$> a_res <*> r_res

-- checkKiConApp
--   :: KiEqFlags -> AnyMonoKind -> KiCon -> [AnyMonoKind] -> TcM (PuResult () Reduction)
-- checkKiConApp flags kc_app kc kis
--   = recurseIntoKiConApp flags kc kis

-- recurseIntoKiConApp :: KiEqFlags -> KiCon -> [AnyMonoKind] -> TcM (PuResult () Reduction)
-- recurseIntoKiConApp flags kc kis = do
--   kis_res <- mapCheck (checkKiEqRhs flags) kis
--   return (mkKiConAppRedn kc <$> kis_res)

checkKiVar :: KiEqFlags -> AnyKiVar -> TcM (PuResult () KiReduction)
checkKiVar (KEF { kef_lhs = lhs, kef_unifying = unifying, kef_occurs = occ_prob }) occ_kv
  = case lhs of
      KiVarLHS lhs_kv -> check_kv unifying lhs_kv
  where
    lvl_occ = handleAnyKv (const topTcLevel) varLevel occ_kv
    success = okCheckReflKi (mkKiVarKi occ_kv)

    check_kv :: AreUnifying -> AnyKiVar -> TcM (PuResult () KiReduction)
    check_kv NotUnifying lhs_kv = simple_occurs_check lhs_kv
    check_kv (Unifying info lvl prom) lhs_kv = do
      mb_done <- handleAnyKv (const (return Nothing)) isFilledMetaKiVar_maybe occ_kv
      case mb_done of
        Just _ -> success
        Nothing -> check_unif info lvl prom lhs_kv

    check_unif :: MetaInfo -> TcLevel -> LevelCheck -> AnyKiVar -> TcM (PuResult a KiReduction)
    check_unif lhs_kv_info lhs_kv_lvl prom lhs_kv
      -- | isConcreteInfo lhs_kv_info
      -- , not (isConcreteVar occ_kv)
      -- = case can_make_concrete occ_kv of
      --     Just tc_occ_kv -> promote lhs_kv lhs_kv_info lhs_kv_lvl tc_occ_kv
      --     Nothing -> failCheckWith (ctkeProblem ctkeConcrete)

      | lvl_occ `strictlyDeeperThan` lhs_kv_lvl
      = case prom of
          LC_None -> pprPanic "check_unif" (ppr lhs_kv $$ ppr occ_kv)
          LC_Check -> failCheckWith (ctkeProblem ctkeSkolemEscape)
          LC_Promote
            | Just tc_occ_kv <- toTcKiVar_maybe occ_kv
            , isSkolemVar tc_occ_kv
              -> failCheckWith (ctkeProblem ctkeSkolemEscape)
            | otherwise
              -> promote lhs_kv lhs_kv_info lhs_kv_lvl 

      | otherwise
      = simple_occurs_check lhs_kv

    simple_occurs_check lhs_kv
      | lhs_kv == occ_kv
      = failCheckWith (ctkeProblem occ_prob)
      | otherwise
      = success

    promote lhs_kv lhs_kv_info lhs_kv_lvl
      | Just tc_occ_kv <- toTcKiVar_maybe occ_kv
      , MetaVar { mv_info = info_occ, mv_tclvl = lvl_occ } <- tcVarDetails tc_occ_kv
      = do let new_info -- | isConcreteInfo lhs_kv_info = lhs_kv_info
                        | otherwise = info_occ
               new_lvl = lhs_kv_lvl `minTcLevel` lvl_occ

           new_kv_ki <- promote_meta_kivar new_info new_lvl tc_occ_kv
           okCheckReflKi new_kv_ki
      | otherwise = pprPanic "promote" (ppr occ_kv)

promote_meta_kivar :: MetaInfo -> TcLevel -> TcKiVar -> TcM AnyMonoKind
promote_meta_kivar info dest_lvl occ_kv = do
  mb_filled <- isFilledMetaKiVar_maybe occ_kv
  case mb_filled of
    Just ki -> return ki
    Nothing -> do new_kv <- toAnyKiVar <$> cloneMetaKiVarWithInfo info dest_lvl occ_kv
                  liftZonkM $ writeMetaKiVar occ_kv (mkKiVarKi new_kv)
                  traceTc "promoteKiVar" (ppr occ_kv <+> text "-->" <+> ppr new_kv)
                  return $ mkKiVarKi new_kv

touchabilityAndShapeTestKind :: TcLevel -> TcKiVar -> AnyMonoKind -> Bool
touchabilityAndShapeTestKind given_eq_lvl kv rhs
  | MetaVar { mv_info = info, mv_tclvl = kv_lvl } <- tcVarDetails kv
  , checkTopShapeKind info rhs
  = kv_lvl `deeperThanOrSame` given_eq_lvl
  | otherwise
  = False

checkTopShapeKind :: MetaInfo -> AnyMonoKind -> Bool
checkTopShapeKind info xi
  = case info of
      VarVar -> case getKiVar_maybe xi of
                  Nothing -> False
                  Just kv -> handleAnyKv (const True) helper kv
      _ -> True
  where
    helper kv = 
      case tcVarDetails kv of
        SkolemVar {} -> True
        MetaVar { mv_info = VarVar } -> True
        _ -> False

touchabilityAndShapeTestType :: TcLevel -> TcTyVar AnyKiVar -> AnyType -> Bool
touchabilityAndShapeTestType given_eq_lvl tv rhs
  | MetaVar { mv_info = info, mv_tclvl = tv_lvl } <- tcVarDetails tv
  , tv_lvl `deeperThanOrSame` given_eq_lvl
  , checkTopShapeType info rhs
  = True
  | otherwise
  = False

checkTopShapeType :: MetaInfo -> AnyType -> Bool
checkTopShapeType info xi
  = case info of
      VarVar -> case getTyVar_maybe xi of
                  Nothing -> False
                  Just tv -> handleAnyTv (const True) helper tv
      _ -> True
  where
    helper tv = case tcVarDetails tv of
                  SkolemVar {} -> True
                  MetaVar { mv_info = VarVar } -> True
                  _ -> False
