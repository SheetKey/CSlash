{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module CSlash.Tc.Gen.CsType where

import Prelude hiding ((<>))

import CSlash.Cs
import CSlash.Rename.Utils
import CSlash.Tc.Gen.CsKind
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Types.BasicTypes
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.LclEnv
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Utils.Env
import CSlash.Tc.Utils.TcMType
import CSlash.Tc.Validity
import CSlash.Tc.Utils.Unify
-- import GHC.IfaceToCore
import CSlash.Tc.Solver
-- import GHC.Tc.Zonk.Type
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Utils.Instantiate ( tcInstInvisibleKiBinder )
import CSlash.Tc.Zonk.TcType

import CSlash.Core.Type
import CSlash.Core.Type.Rep
import CSlash.Core.Type.Ppr
import CSlash.Core.Kind
import CSlash.Core.Kind.Compare
import CSlash.Core.Kind.Subst
import CSlash.Core.Kind.FVs

import CSlash.Builtin.Types.Prim
import CSlash.Types.Error
import CSlash.Types.Name.Env
import CSlash.Types.Name.Reader( lookupLocalRdrOcc )
import CSlash.Types.Var
import CSlash.Types.Var.Set
import CSlash.Core.TyCon
import CSlash.Core.ConLike
import CSlash.Core.DataCon
-- import CSlash.Core.Class
import CSlash.Types.Name
import CSlash.Types.Var.Env
import CSlash.Builtin.Types
import CSlash.Types.Basic
import CSlash.Types.SrcLoc
import CSlash.Types.Unique
import CSlash.Types.Unique.FM
import CSlash.Utils.Misc
import CSlash.Types.Unique.Supply
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Builtin.Names hiding ( wildCardName )
import CSlash.Driver.DynFlags

import CSlash.Data.FastString
import CSlash.Data.List.Infinite ( Infinite (..) )
import qualified CSlash.Data.List.Infinite as Inf
import CSlash.Data.List.SetOps
import CSlash.Data.Maybe
import CSlash.Data.Bag( unitBag )

import Data.Function ( on )
import Data.List.NonEmpty ( NonEmpty(..), nonEmpty )
import qualified Data.List.NonEmpty as NE
import Data.List ( mapAccumL )
import Control.Monad
import Data.Tuple( swap )

import Data.Coerce (coerce)
import Control.Arrow (first)

{- *********************************************************************
*                                                                      *
              Check types AND do validity checking
*                                                                      *
********************************************************************* -}

addSigCtxt :: Outputable cs_ty => UserTypeCtxt -> LocatedA cs_ty -> TcM a -> TcM a
addSigCtxt ctxt cs_ty thing_inside = setSrcSpan (getLocA cs_ty)
                                     $ addErrCtxt (pprSigCtxt ctxt cs_ty)
                                     $ thing_inside

pprSigCtxt :: Outputable cs_ty => UserTypeCtxt -> LocatedA cs_ty -> SDoc
pprSigCtxt ctxt cs_ty
  | Just n <- isSigMaybe ctxt
  = hang (text "In the type signature:")
    2 (pprPrefixOcc n <+> colon <+> ppr cs_ty)
  | otherwise
  = hang (text "In" <+> pprUserTypeCtxt ctxt <> colon)
    2 (ppr cs_ty)

tcCsSigType :: UserTypeCtxt -> LCsSigType Rn -> TcM AnyType
tcCsSigType ctxt sig_ty = addSigCtxt ctxt sig_ty $ do
  traceTc "tcCsSigType {" (ppr sig_ty)
  let skol_info = SigTypeSkol ctxt
  skol_info <- mkSkolemInfo skol_info

  (implic, ty) <- tc_lcs_sig_type skol_info sig_ty (expectedKindInCtxt ctxt)

  traceTc "tcCsSigType 2" (ppr implic)
  simplifyAndEmitFlatConstraints (mkKiImplicWC (unitBag implic))

  ty <- liftZonkM $ zonkTcType ty
  checkValidType ctxt ty
  traceTc "end tcCsSigType }" (ppr ty)
  return ty

tc_lcs_sig_type :: SkolemInfo -> LCsSigType Rn -> ContextKind -> TcM (KiImplication, AnyType)
tc_lcs_sig_type skol_info full_cs_ty@(L loc (CsSig { sig_ext = kv_nms
                                                   , sig_body = cs_ty })) ctxt_kind
  = setSrcSpanA loc $ do
  (tc_lvl, wanted, (kv_bndrs, (exp_kind, ty)))
    <- pushLevelAndSolveKindCoercionsX "tc_lcs_sig_type"
       $ tcImplicitKiBndrs skol_info kv_nms $ do
         exp_kind <- newExpectedKind ctxt_kind
         stuff <- tcLCsType cs_ty exp_kind
         return (exp_kind, stuff)

  traceTc "tc_lcs_sig_type" (ppr tc_lvl $$ ppr exp_kind $$ ppr ty)

  -- exp_kind_vars are (afaik) all compiler generated (not user written)
  exp_kind_vars <- candidateQKiVarsOfKind (Mono exp_kind)
  doNotQuantifyKiVars exp_kind_vars

  -- the kv_bndrs are all of the user writen ki vars occuring in the user written type sig
  traceTc "tc_lcs_sig_type" (ppr kv_nms $$ ppr kv_bndrs)
  kv_bndrs <- liftZonkM $ zonkTcKiVarsToTcKiVars kv_bndrs
  traceTc "tc_lcs_sig_type" (text "zonked kv_bndrs" <+> ppr kv_bndrs)

  let ty1 = mkBigLamTys (toAnyKiVar <$> kv_bndrs) ty
  -- catch any kind variables that were not user written
  kvs <- kindGeneralizeSome skol_info wanted ty1

  implic <- buildKvImplication (getSkolemInfo skol_info) kvs tc_lvl wanted

  return (implic, mkBigLamTys (toAnyKiVar <$> kvs) ty1)

{- *********************************************************************
*                                                                      *
             The main kind checker (no validity checks)
*                                                                      *
********************************************************************* -}

tcCheckLCsType :: LCsType Rn -> ContextKind -> TcM AnyType
tcCheckLCsType cs_ty exp_kind = addTypeCtxt cs_ty $ do
  ek <- newExpectedKind exp_kind
  tcLCsType cs_ty ek

------------------------------------------
tc_infer_lcs_type :: LCsType Rn -> TcM (AnyType, AnyMonoKind)
tc_infer_lcs_type (L span ty) = setSrcSpanA span $ tc_infer_cs_type ty

---------------------------
tc_infer_cs_type_ek :: HasDebugCallStack => CsType Rn -> AnyMonoKind -> TcM AnyType
tc_infer_cs_type_ek cs_ty ek = do
  (ty, k) <- tc_infer_cs_type cs_ty
  checkExpectedKind cs_ty ty k ek

---------------------------
tc_infer_cs_type :: CsType Rn -> TcM (AnyType, AnyMonoKind)

tc_infer_cs_type (CsParTy _ ty) = tc_infer_lcs_type ty

tc_infer_cs_type ty
  | Just (cs_fun_ty, cs_args) <- splitCsAppTys ty
  = do fun_ty <- tcInferTyAppHead cs_fun_ty
       tcInferTyApps cs_fun_ty fun_ty cs_args

tc_infer_cs_type (CsKindSig _ ty sig) = do
  sig' <- tcLCsKindSig KindSigCtxt sig
  traceTc "tc_infer_cs_type:sig" (ppr ty $$ ppr sig')
  ty' <- tc_lcs_type ty sig'
  return (ty', sig')

tc_infer_cs_type other_ty = do
  kv <- asAnyKi <$> newMetaKindVar
  ty' <- tc_cs_type other_ty kv
  return (ty', kv)

------------------------------------------
tcLCsType :: LCsType Rn -> AnyMonoKind -> TcM AnyType
tcLCsType = tc_lcs_type

tc_lcs_type :: LCsType Rn -> AnyMonoKind -> TcM AnyType
tc_lcs_type (L span ty) exp_kind = setSrcSpanA span $
  tc_cs_type ty exp_kind

tc_cs_type :: CsType Rn -> AnyMonoKind -> TcM AnyType

tc_cs_type (CsParTy _ ty) exp_kind = tc_lcs_type ty exp_kind

tc_cs_type (CsFunTy _ arr_kind ty1 ty2) exp_kind
  = tc_fun_type arr_kind ty1 ty2 exp_kind

tc_cs_type t@(CsForAllTy { cst_tele = tele, cst_body = ty }) exp_kind
  = tc_cs_forall_ty tele ty exp_kind
  where
    tc_cs_forall_ty tele ty ek = do
      (tv_bndrs, ty') <- tcTelescope tele $ tc_lcs_type ty exp_kind
      return $ mkForAllTys (mapVarBinder toAnyTyVar <$> tv_bndrs) ty'

tc_cs_type rn_ty@(CsQualTy { cst_ctxt = ctxt, cst_body = body_ty }) exp_kind
  | null (unLoc ctxt)
  = tc_lcs_type body_ty exp_kind
  | otherwise
  = do let (ctxt_kis, _) = splitInvisFunKis exp_kind
       massertPpr (ctxt_kis `equalLength` unLoc ctxt)
         $ vcat [ text "tc_cs_type CsQualTy", ppr ctxt, ppr exp_kind ]
       (coVars, coVarKis) <- tcLCsContext ctxt
       traceTc "tc_cs_type CsQualTy"
         $ vcat [ ppr rn_ty, ppr coVars ]
       (ty', body_ki) <- checkKiConstraints InferKindSkol coVars
                         $ tc_infer_lcs_type body_ty
       let final_ty = mkTyLamTys (toAnyTyVar <$> coVars) ty'
           final_ki = mkInvisFunKis coVarKis body_ki
       checkExpectedKind rn_ty final_ty final_ki exp_kind

tc_cs_type rn_ty@(CsTupleTy _ tup_args) exp_kind
  | all tyTupArgPresent tup_args
  = tc_tuple rn_ty exp_kind
  | otherwise
  = panic "tc_cs_type missing ty tup_args"
  where
    tyTupArgPresent (TyPresent {}) = True
    tyTupArgPresent (TyMissing {}) = False

tc_cs_type rn_ty@(CsSumTy _ cs_tys) exp_kind = do
  let arity = length cs_tys
  arg_kinds <- mapM (\_ -> newOpenTypeKind) cs_tys
  tau_tys <- zipWithM tc_lcs_type cs_tys (asAnyKi <$> arg_kinds)
  let sum_ty = mkTyConApp (asAnyTyKi $ sumTyCon arity) tau_tys
      sum_kind = panic "sum_kind"
  checkExpectedKind rn_ty sum_ty sum_kind exp_kind

tc_cs_type ty@(CsTyLamTy _ matches) ek = tcTyLamMatches ty matches ek

tc_cs_type ty@(CsTyVar {}) ek = tc_infer_cs_type_ek ty ek
tc_cs_type ty@(CsAppTy {}) ek = tc_infer_cs_type_ek ty ek
tc_cs_type ty@(CsOpTy {}) ek = tc_infer_cs_type_ek ty ek
tc_cs_type ty@(CsKindSig {}) ek = tc_infer_cs_type_ek ty ek

tc_cs_type ty@(TySectionL {}) _ = pprPanic "tc_cs_type" (ppr ty)
tc_cs_type ty@(TySectionR {}) _ = pprPanic "tc_cs_type" (ppr ty)

tc_cs_type other _ = pprPanic "tc_cs_type unfinished" (ppr other)

------------------------------------------
tc_fun_type :: CsArrow Rn -> LCsType Rn -> LCsType Rn -> AnyMonoKind -> TcM AnyType
tc_fun_type arr_kind ty1 ty2 exp_kind = do
  traceTc "tc_fun_type" (ppr ty1 $$ ppr ty2)
  arg_k <- newOpenTypeKind
  res_k <- newOpenTypeKind
  ty1' <- tc_lcs_type ty1 (asAnyKi arg_k)
  ty2' <- tc_lcs_type ty2 (asAnyKi res_k)
  arr_kind' <- tc_arrow arr_kind
  checkExpectedKind (CsFunTy noExtField arr_kind ty1 ty2)
                    (tcMkFunTy arr_kind' ty1' ty2')
                    arr_kind' exp_kind

tc_arrow :: CsArrow Rn -> TcM AnyMonoKind
tc_arrow (CsArrow _ (L _ ki)) = tcArrow ki

{- *********************************************************************
*                                                                      *
                Tuples
*                                                                      *
********************************************************************* -}

-- tc_tuple :: CsType Rn -> TcMonoKind -> TcM TcType
-- tc_tuple rn_ty@(CsTupleTy _ tup_args) exp_kind = do
--   let arity = length tys
--       tys = (\case { TyPresent _ ty -> ty; _ -> panic "tc_tuple" }) <$> tup_args
--   arg_kinds <- replicateM arity newOpenTypeKind
--   tau_tys <- zipWithM tc_lcs_type tys arg_kinds
--   finish_tuple rn_ty tau_tys arg_kinds exp_kind
-- tc_tuple _ _ = panic "tc_tuple/unreachable"

-- finish_tuple :: CsType Rn -> [TcType] -> [TcMonoKind] -> TcMonoKind -> TcM TcType
-- finish_tuple rn_ty tau_tys tau_kinds exp_kind = do
--   traceTc "finish_tuple" (ppr tau_kinds $$ ppr exp_kind)
--   let arity = length tau_tys
--       tycon = tupleTyCon arity
--       res_kind = panic "tyConResKind tycon"
--   checkTupSize arity
--   checkExpectedKind rn_ty (mkTyConApp tycon tau_tys) res_kind exp_kind

tc_tuple :: CsType Rn -> AnyMonoKind -> TcM AnyType
tc_tuple rn_ty@(CsTupleTy _ tup_args) exp_kind = do
  let arity = length tup_args
      tup_tycon = asAnyTyKi $ tupleTyCon arity
  (ty, res_kind) <- inst_tuple_tycon tup_tycon tup_args
  checkExpectedKind rn_ty ty res_kind exp_kind
tc_tuple _ _ = panic "tc_tuple/unreachable"

inst_tuple_tycon :: AnyTyCon -> [CsTyTupArg Rn] -> TcM (AnyType, AnyMonoKind)
inst_tuple_tycon tup_tycon tup_args = do
  traceTc "inst_tuple_tycon {" (ppr tup_tycon $$ ppr tup_args)
  (res, res_ki) <- go_init 1 tup_tycon tup_args
  traceTc "inst_tuple_tycon }" (ppr res $$ ppr res_ki)
  return (res, res_ki)
  where
    go_init n tup_tycon all_args = case tup_ki of
                                     Mono _ -> pprPanic "inst_tuple_tycon/MonoTupKi" (ppr tup_ki)
                                     _ -> go n tup_type empty_subst tup_ki all_args
      where
        tup_ki = tyConKind tup_tycon
        tup_type = tyConNullaryTy tup_tycon
        empty_subst = mkEmptyKvSubst $ mkInScopeSet $ varsOfKind tup_ki

    go
      :: Int
      -> AnyType
      -> KvSubst AnyKiVar
      -> AnyKind
      -> [CsTyTupArg Rn]
      -> TcM (AnyType, AnyMonoKind)
    go n fun subst fun_ki all_args = case tcSplitForAllKi_maybe fun_ki of
      Just (ki_binder, inner_ki) -> do
        traceTc "inst_tuple_tycon (need to instantiate)"
          $ vcat [ ppr ki_binder, ppr subst ]
        (subst', arg') <- tcInstInvisibleKiBinder subst ki_binder
        go n (mkAppTy fun arg') subst' inner_ki all_args

      Nothing | Mono mono_fun_ki <- fun_ki -> go_mono_invis n fun subst mono_fun_ki all_args
              | otherwise -> pprPanic "inst_tuple_tycon"
                             $ vcat [ ppr fun, ppr subst, ppr fun_ki, ppr all_args ]

    go_mono_invis
      :: Int
      -> AnyType
      -> KvSubst AnyKiVar
      -> AnyMonoKind
      -> [CsTyTupArg Rn]
      -> TcM (AnyType, AnyMonoKind)
    go_mono_invis n fun subst fun_ki all_args = case splitInvisFunKis fun_ki of
      ([], _) -> pprPanic "inst_tuple_tycon/go_mono_invis"
                 $ vcat [ ppr fun, ppr subst, ppr fun_ki, ppr all_args ]
      (theta, inner_ki) -> do
        let inst_theta = substMonoKis subst theta
        kiCos <- instCallKiConstraints TupleTyOrigin inst_theta
        go_mono n (mkAppTys fun (KindCoercion <$> kiCos)) subst inner_ki all_args

    go_mono
      :: Int
      -> AnyType
      -> KvSubst AnyKiVar
      -> AnyMonoKind
      -> [CsTyTupArg Rn]
      -> TcM (AnyType, AnyMonoKind)
    go_mono n fun subst fun_ki all_args = case (all_args, tcSplitMonoFunKi_maybe fun_ki) of
      ([], Nothing) -> return (fun, substMonoKi subst fun_ki)
      ([], _) -> pprPanic "inst_tuple_tycon/unreachable1"
                 $ vcat [ ppr fun, ppr subst, ppr fun_ki ]

      (TyPresent _ arg : args, Just (af, arg_ki, res_ki)) ->
        assertPpr (isVisibleKiFunArg af)
        (vcat [ text "inst_tuple_tycon/go_mono/present case has invisible arg kind"
              , ppr fun, ppr fun_ki, ppr all_args
              ])
        $ do traceTc "inst_tuple_tycon (vis present app)"
               $ vcat [ ppr arg_ki, ppr arg, ppr subst ]
             let arg_exp_kind = substMonoKi subst arg_ki
             arg' <- addErrCtxt (tupAppCtxt arg n)
                     $ tc_lcs_type arg arg_exp_kind
             traceTc "inst_tuple_tycon (vis present app) 2" (ppr arg_ki)
             fun' <- mkAppTyM fun arg_ki arg'
             go_mono (n + 1) fun' subst res_ki args

      (TyMissing _ : args, Just (af, arg_ki, res_ki)) -> panic "type tuple sections in the works"

      (_:_, Nothing) -> pprPanic "inst_tuple_tycon/unreachable1"
                        $ vcat [ ppr fun, ppr subst, ppr fun_ki, ppr all_args ]

---------------------------
tcInferTyApps :: LCsType Rn -> AnyType -> [LCsTypeArg Rn] -> TcM (AnyType, AnyMonoKind)
tcInferTyApps cs_ty fun cs_args = do
  --(f_args, res_k) <- tcInferTyApps_nosat cs_ty fun cs_args
  --saturateFamApp f_args res_k
  tcInferTyApps_nosat cs_ty fun cs_args

tcInferTyApps_nosat :: LCsType Rn -> AnyType -> [LCsTypeArg Rn] -> TcM (AnyType, AnyMonoKind)
tcInferTyApps_nosat orig_cs_ty fun orig_cs_args = do
  traceTc "tcInferTyApps {" (ppr orig_cs_ty $$ ppr orig_cs_args)
  (f_args, res_k) <- go_init 1 fun orig_cs_args
  traceTc "tcInferTyApps }" (ppr f_args <+> colon <+> ppr res_k)
  return (f_args, res_k)
  where
    go_init n fun all_args = case fun_ki of
                               Mono mki -> go_mono n fun empty_subst mki all_args
                               _ -> go n fun empty_subst fun_ki all_args
      where
        fun_ki = typeKind fun
        empty_subst = mkEmptyKvSubst $ mkInScopeSet $ varsOfKind fun_ki

    go
      :: Int
      -> AnyType
      -> KvSubst AnyKiVar
      -> AnyKind
      -> [LCsTypeArg Rn]
      -> TcM (AnyType, AnyMonoKind)
    go n fun subst fun_ki all_args = case tcSplitForAllKi_maybe fun_ki of
      -- need to instantiate invisible kind var
      Just (ki_binder, inner_ki) -> do
        traceTc "tcInferTyApps (need to instantiate)"
          $ vcat [ ppr ki_binder, ppr subst ]
        (subst', arg') <- tcInstInvisibleKiBinder subst ki_binder
        go n (mkAppTy fun arg') subst' inner_ki all_args

      _ | Mono mono_fun_ki <- fun_ki -> go_mono_invis n fun subst mono_fun_ki all_args

      _ -> pprPanic "tcInferTyApps_nosat"
           $ vcat [ ppr fun
                  , ppr subst
                  , ppr fun_ki
                  , ppr all_args ]

    go_mono_invis
      :: Int
      -> AnyType
      -> KvSubst AnyKiVar
      -> AnyMonoKind
      -> [LCsTypeArg Rn]
      -> TcM (AnyType, AnyMonoKind)
    go_mono_invis n fun subst fun_ki all_args = case splitInvisFunKis fun_ki of
      ([], _) -> go_mono n fun subst fun_ki all_args
      (theta, inner_ki) -> do
        let inst_theta = substMonoKis subst theta
            orig = lCsTyCtOrigin orig_cs_ty
        kiCos <- instCallKiConstraints orig inst_theta
        traceTc "tcInferTyApps (invis app)"
          $ vcat [ text "theta:" <+> ppr theta
                 , text "inner_ki:" <+> ppr inner_ki
                 , text "subst:" <+> ppr subst
                 , text "inst_theta:" <+> ppr inst_theta
                 , text "kiCos:" <+> ppr kiCos ]
        go_mono n (mkAppTys fun (KindCoercion <$> kiCos)) subst inner_ki all_args

    go_mono
      :: Int
      -> AnyType
      -> KvSubst AnyKiVar
      -> AnyMonoKind
      -> [LCsTypeArg Rn]
      -> TcM (AnyType, AnyMonoKind)
    go_mono n fun subst fun_ki all_args = case (all_args, tcSplitMonoFunKi_maybe fun_ki) of
      ([], _) -> return (fun, substMonoKi subst fun_ki)

      (CsArgPar _ : args, _) -> go_mono n fun subst fun_ki args

      -- "normal" case 
      (CsValArg _ arg : args, Just (af, arg_ki, res_ki)) ->
        assertPpr (isVisibleKiFunArg af)
        (vcat [ text "tcInferTyApps_nosat/go_mono/normal case has invisible arg kind"
              , ppr fun, ppr fun_ki, ppr all_args
              ])
        $ do traceTc "tcInferTyApps (vis normal app)"
               $ vcat [ ppr arg_ki, ppr arg, ppr subst ]
             let arg_exp_kind = substMonoKi subst arg_ki
             arg' <- addErrCtxt (funAppCtxt orig_cs_ty arg n)
                     $ tc_lcs_type arg arg_exp_kind
             traceTc "tcInferTyApps (vis normal app) 2" (ppr arg_ki)
             fun' <- mkAppTyM fun arg_ki arg'
             go_mono (n + 1) fun' subst res_ki args

      (CsValArg _ _ : _, Nothing) -> try_again_after_substing_or $ do
        let arrows_needed = n_initial_val_args all_args
        co <- matchExpectedFunKind (CsTypeRnThing $ unLoc cs_ty) arrows_needed substed_fun_ki

        fun' <- liftZonkM $ zonkTcType (fun `mkCastTy` co)

        traceTc "tcInferTyApps (no binder)"
          $ vcat [ ppr fun <+> colon <+> ppr fun_ki
                 , ppr arrows_needed
                 , ppr co
                 , ppr fun' <+> colon <+> ppr (typeKind fun') ]

        go_init n fun' all_args

      -- visible kind application in user code (not possible)
      (CsTypeArg {} : _, _) -> panic "tcInferTyApps/go_mono/CsTypeArg"

      where
        try_again_after_substing_or fallthrough
          | not (isEmptyKvSubst subst)
          = go_mono n fun zapped_subst substed_fun_ki all_args
          | otherwise
          = fallthrough

        zapped_subst = zapKvSubst subst
        substed_fun_ki = substMonoKi subst fun_ki
        cs_ty = appTypeToArg orig_cs_ty (take (n-1) orig_cs_args)

    n_initial_val_args :: [CsArg p tm ty] -> Arity
    n_initial_val_args (CsValArg {} : args) = 1 + n_initial_val_args args
    n_initial_val_args (CsArgPar {} : args) = n_initial_val_args args
    n_initial_val_args _ = 0

instCallKiConstraints :: CtOrigin -> [AnyPredKind] -> TcM [AnyKindCoercion]
instCallKiConstraints orig preds
  | null preds
  = return []
  | otherwise
  = do kcos <- mapM go preds
       traceTc "instCallKiConstraints" (ppr kcos)
       return kcos
  where
    go :: AnyPredKind -> TcM AnyKindCoercion
    go pred
      | KiPredApp kc k1 k2 <- pred
      = unifyKind Nothing kc k1 k2
      | otherwise
      = panic "instCallKiConstraints"

mkAppTyM :: AnyType -> AnyMonoKind -> AnyType -> TcM AnyType
mkAppTyM fun arg_ki arg
  | TyConApp tc args <- fun
  , isTypeSynonymTyCon tc
  , args `lengthIs` (tyConArity tc - 1)
  = do (arg':args') <- liftZonkM $ panic "zonkTcTypes (arg:args)"
       return $ panic "mkTyConApp tc (args' ++ [arg'])"

mkAppTyM fun arg_ki arg = return $ mk_app_ty fun arg

mk_app_ty :: AnyType -> AnyType -> AnyType
mk_app_ty fun arg = assertPpr (isFunKi fun_kind)
                              (ppr fun <+> colon <+> ppr fun_kind $$ ppr arg)
                    $ mkAppTy fun arg
  where fun_kind = typeKind fun

-- saturateFamApp :: TcType -> TcKind -> TcM (TcType, TcKind)
-- saturateFamApp ty kind 
--   | Just (tc, args) <- tcSplitTyConApp_maybe ty
--   , tyConMustBeSaturated tc
--   , let n_to_inst = tyConArity tc - length args
--   = do (extra_args, ki') <- tcInstInvisibleTyBindersN n_to_inst kind
--        return (ty `mkAppTys` extra_args, ki')
--   | otherwise
--   = return (ty, kind)

appTypeToArg :: LCsType Rn -> [LCsTypeArg Rn] -> LCsType Rn
appTypeToArg f [] = f
appTypeToArg f (CsValArg _ arg : args) = appTypeToArg (mkCsAppTy f arg) args
appTypeToArg f (CsArgPar _ : args) = appTypeToArg f args
appTypeToArg f args@(CsTypeArg _ _ : _) = pprPanic "appTypeToArg" $ vcat [ ppr f, ppr args ]


{- *********************************************************************
*                                                                      *
                Type applications
*                                                                      *
********************************************************************* -}

splitCsAppTys :: CsType Rn -> Maybe (LCsType Rn, [LCsTypeArg Rn])
splitCsAppTys cs_ty
  | is_app cs_ty = Just $ go (noLocA cs_ty) []
  | otherwise = Nothing
  where
    is_app :: CsType Rn -> Bool
    is_app (CsAppTy {}) = True
    is_app (CsOpTy _ _ (L _ op) _) = not (op `hasKey` fUNTyConKey)
    is_app (CsTyVar {}) = True
    is_app (CsParTy _ (L _ ty)) = is_app ty
    is_app (CsUnboundTyVar {}) = True
    is_app _ = False

    go :: LCsType Rn -> [LCsTypeArg Rn] -> (LCsType Rn, [LCsTypeArg Rn])
    go (L _ (CsAppTy _ f a)) as = go f (CsValArg noExtField a : as)
    go (L sp (CsParTy _ f)) as = go f (CsArgPar (locA sp) : as)
    go (L _ (CsOpTy _ l op@(L sp _) r)) as
      = ( L (l2l sp) (CsTyVar noAnn op)
        , CsValArg noExtField l : CsValArg noExtField r : as )
    go f as = (f, as)

---------------------------
tcInferTyAppHead :: LCsType Rn -> TcM AnyType
tcInferTyAppHead (L _ (CsTyVar _ (L _ tv))) = tcTyVar tv
tcInferTyAppHead (L _ (CsUnboundTyVar _ _)) = panic "tcInferTyAppHead/unbound ty var"
tcInferTyAppHead ty = fst <$> tc_infer_lcs_type ty

{- *********************************************************************
*                                                                      *
                TyLamTy
*                                                                      *
********************************************************************* -}

tcTyLamMatches :: CsType Rn -> MatchGroup Rn (LCsType Rn) -> AnyMonoKind -> TcM AnyType
tcTyLamMatches cs_type (MG _
                (L _
                 [L _
                  (Match _
                         TyLamTyAlt
                         (L _ pats)
                         (GRHSs _ [L _ (GRHS _ [] body_ty)]))]))
  exp_kind = do
  (bndrs, (body_ty', inf_ki)) <- tcTyLamTyBndrs pats $ tc_infer_lcs_type body_ty

  let bndr_kinds = varKind <$> bndrs
      act_kind = mkVisFunKis bndr_kinds inf_ki
      full_ty = mkTyLamTys (toAnyTyVar <$> bndrs) body_ty'

  checkExpectedKind cs_type full_ty act_kind exp_kind

tcTyLamMatches _ _ _ = panic "unreachable"

{- *********************************************************************
*                                                                      *
                checkExpectedKind
*                                                                      *
********************************************************************* -}

checkExpectedKind
  :: HasDebugCallStack
  => CsType Rn
  -> AnyType
  -> AnyMonoKind
  -> AnyMonoKind
  -> TcM AnyType
checkExpectedKind cs_ty ty act_kind exp_kind = do
  traceTc "checkExpectedKind" (ppr ty $$ ppr act_kind)

  let origin = KindCoOrigin { kco_actual = act_kind
                            , kco_expected = exp_kind
                            , kco_pred = EQKi
                            , kco_thing = Just $ CsTypeRnThing cs_ty
                            , kco_visible = True }

  traceTc "checkExpectedKindX"
    $ vcat [ ppr cs_ty
           , text "act_kind:" <+> ppr act_kind
           , text "exp_kind:" <+> ppr exp_kind ]

  if act_kind `tcEqMonoKind` exp_kind
    then return ty
    else do co_k <- unifyKindAndEmit origin EQKi act_kind exp_kind
            traceTc "checkExpectedKind"
              $ vcat [ ppr act_kind, ppr exp_kind, ppr co_k ]
            return (ty `mkCastTy` co_k)

tcTyVar :: Name -> TcM AnyType
tcTyVar name = do
  traceTc "lk1" (ppr name)
  thing <- tcLookup name
  case thing of
    ATyVar _ tv -> return $ mkTyVarTy (toAnyTyVar tv)
    (tcTyThingTyCon_maybe -> Just tc) -> return $ mkTyConTy tc
    
    _ -> wrongThingErr WrongThingType thing name

addTypeCtxt :: LCsType Rn -> TcM a -> TcM a
addTypeCtxt (L _ ty) thing = addErrCtxt doc thing
  where
    doc = text "In the type" <+> quotes (ppr ty)

addKindCtxt :: LCsKind Rn -> TcM a -> TcM a
addKindCtxt (L _ ki) thing = addErrCtxt doc thing
  where
    doc = text "In the kind" <+> quotes (ppr ki)

{- *********************************************************************
*                                                                      *
             Kind inference for type declarations
*                                                                      *
********************************************************************* -}

data InitialKindStrategy
  = InitialKindInfer

kcDeclHeader
  :: InitialKindStrategy
  -> Name
  -> TyConFlavor
  -> [Name]
  -> TcM ContextKind
  -> TcM MonoAnyTyCon
kcDeclHeader InitialKindInfer = kcInferDeclHeader

kcInferDeclHeader
  :: Name
  -> TyConFlavor
  -> [Name]
  -> TcM ContextKind
  -> TcM MonoAnyTyCon
kcInferDeclHeader name flav kv_ns kc_res_ki = addTyConFlavCtxt name flav $ do
  skol_info <- mkSkolemInfo (TyConSkol flav name)
  (scoped_kvs, res_kind) <- bindImplicitKBndrs_Q_Skol skol_info kv_ns
                            $ newExpectedKind =<< kc_res_ki

  let kv_pairs = mkVarNamePairs scoped_kvs
      arity = length $ fst $ splitFunKis res_kind
      tycon = mkTcTyCon name (Mono res_kind) arity kv_pairs False flav
  
  traceTc "kcInferDeclHeader"
    $ vcat [ ppr name, ppr kv_ns, ppr scoped_kvs, ppr res_kind, ppr arity ]

  return tycon

{- *********************************************************************
*                                                                      *
             Expected kinds
*                                                                      *
********************************************************************* -}

data ContextKind
  = TheMonoKind AnyMonoKind
  | AnyMonoKind

newExpectedKind :: ContextKind -> TcM AnyMonoKind
newExpectedKind (TheMonoKind k) = return k
newExpectedKind AnyMonoKind = asAnyKi <$> newMetaKindVar

expectedKindInCtxt :: UserTypeCtxt -> ContextKind
expectedKindInCtxt _ = AnyMonoKind

{- *********************************************************************
*                                                                      *
             Scoped tykivars that map to the same thing
*                                                                      *
********************************************************************* -}

checkForDuplicateScopedTyVars :: [(Name, AnyTyVar AnyKiVar)] -> TcM ()
checkForDuplicateScopedTyVars scoped_prs
  = unless (null err_prs) $ do
      mapM_ report_dup err_prs
      failM
  where 
    err_prs :: [(Name, Name)]
    err_prs = [ (n1, n2)
              | prs {-:: NonEmpty (Name, TypeVar)-} <- findDupsEq ((==) `on` snd) scoped_prs
              , (n1, _) :| ((n2, _) : _) <- [NE.nubBy ((==) `on` fst) prs ] ]

    report_dup :: (Name, Name) -> TcM ()
    report_dup (n1, n2) = setSrcSpan (getSrcSpan n2)
                          $ addErrTc $ panic "TcRnDifferentNamesForTyVar n1 n2"

{- *********************************************************************
*                                                                      *
             Bringing type variables into scope
*                                                                      *
********************************************************************* -}

--------------------------------------
--    HsForAllTelescope
--------------------------------------

tcTelescope :: CsForAllTelescope Rn -> TcM a -> TcM ([TcTyVarBinder], a)
tcTelescope (CsForAll { csf_bndrs = bndrs }) thing_inside = do
  skol_info <- mkSkolemInfo $ ForAllSkol $ CsTyVarBndrsRn $ unLoc <$> bndrs
  let skol_mode = smVanilla { sm_clone = False, sm_var = SMDSkolemVar skol_info }
  tcExplicitBndrsX skol_mode bndrs thing_inside

--------------------------------------
--    TyLamTy binders
--------------------------------------

tcTyLamTyBndrs :: [LPat Rn] -> TcM a -> TcM ([TcTyVar AnyKiVar], a)
tcTyLamTyBndrs pats thing_inside = do
  let bndrs = explicitTvsFromPats pats
  skol_info <- mkSkolemInfo $ TyLamTySkol $ fmap fst bndrs
  let skol_mode = smVanilla { sm_clone = False, sm_var = SMDSkolemVar skol_info }
  case nonEmpty bndrs of
    Nothing -> do
      res <- thing_inside
      return ([], res)
    Just bndrs1 -> do bindTyLamTyBndrsX skol_mode bndrs thing_inside
      -- (tclvl, wanted, (skol_tvs, res))
      --   <- pushLevelAndCaptureConstraints
      --      $ bindTyLamTyBndrsX skol_mode bndrs thing_inside
      -- let bndr_1 = head pats
      --     bndr_n = last pats
      -- traceTc "tcTyLamTyBndrs/emitResidualTvConstraint"
      --   $ vcat [ ppr skol_tvs, ppr wanted ]
      -- setSrcSpan (combineSrcSpans (getLocA bndr_1) (getLocA bndr_n))
      --   $ emitResidualTvConstraint skol_info skol_tvs tclvl wanted
      -- return (skol_tvs, res)

bindTyLamTyBndrs :: [LPat Rn] -> TcM a -> TcM ([TcTyVar TcKiVar], a)
bindTyLamTyBndrs pats thing_inside = do
  let tvs = explicitTvsFromPats pats
      skol_mode = smVanilla { sm_clone = False, sm_var = SMDVarVar }
  panic "bindTyLamTyBndrsX skol_mode tvs thing_inside"

bindTyLamTyBndrsX :: SkolemMode -> [(Name, Maybe (LCsKind Rn))] -> TcM a -> TcM ([TcTyVar AnyKiVar], a) 
bindTyLamTyBndrsX skol_mode@(SM { sm_kind = ctxt_kind }) cs_tvs thing_inside = do
  traceTc "bindTyLamTyBndrs" (ppr cs_tvs)
  go cs_tvs
  where
    go [] = do
      res <- thing_inside
      return ([], res)
    go ((name, mb_cs_kind) : cs_tvs) = do
      lcl_env <- getLclTyKiEnv
      tv <- tc_cs_bndr lcl_env name mb_cs_kind
      (tvs, res) <- tcExtendNameTyVarEnv [(name, toAnyTyVar tv)]
                    $ go cs_tvs
      return (tv : tvs, res)

    tc_cs_bndr lcl_env name mb_cs_kind
      = case mb_cs_kind of
          Just lcs_kind -> do kind <- tcLCsKindSig (TyVarBndrKindCtxt name) lcs_kind
                              newTyVarBndr skol_mode name kind
          Nothing -> do kind <- newExpectedKind ctxt_kind
                        newTyVarBndr skol_mode name kind

explicitTvsFromPats :: [LPat Rn] -> [(Name, Maybe (LCsKind Rn))]
explicitTvsFromPats = catMaybes . map explicitTvFromPat

explicitTvFromPat :: LPat Rn -> Maybe (Name, Maybe (LCsKind Rn))
explicitTvFromPat = go . unLoc
  where
    go :: Pat Rn -> Maybe (Name, Maybe (LCsKind Rn))
    go (WildPat {}) = Nothing
    go (TyVarPat _ (L _ name)) = Just (name, Nothing)
    go (ParPat _ pat) = go (unLoc pat)
    go (KdSigPat _ pat ki) = case go (unLoc pat) of
                               Just (name, Nothing) -> Just (name, Just (cspsk_body ki))
                               other -> pprPanic "explicitTvFromPat" (ppr other)
    go other = pprPanic "explicitTvFromPat" (ppr other)
    
--------------------------------------
--    Explicit tyvar binders
--------------------------------------

tcExplicitBndrsX :: SkolemMode -> [LCsTyVarBndr Rn] -> TcM a -> TcM ([TcTyVarBinder], a)
tcExplicitBndrsX skol_mode bndrs thing_inside = case nonEmpty bndrs of
  Nothing -> do
    res <- thing_inside
    return ([], res)
  Just bndrs1 -> bindExplicitBndrsX skol_mode bndrs thing_inside

    {- NOTE:
       The following was done in GHC to prevent skolem escape.
       We don't have that problem, since types and kinds are distinct,
       and kinds can't be quantified by the user.
       Thus, we DO NOT need to pushLevelAndCaptureConstraints forllowed by
       emitResidualTvConstraint.
    -}
    -- (tclvl, wanted, (skol_tvs, res))
    --   <- pushLevelAndCaptureConstraints
    --      $ bindExplicitBndrsX skol_mode bndrs
    --      $ thing_inside
    -- let bndr_1 = NE.head bndrs1
    --     bndr_n = NE.last bndrs1
    -- skol_info <- mkSkolemInfo $ ForAllSkol $ CsTyVarBndrsRn (unLoc <$> bndrs)
    -- traceTc "tcExplicitBndrsX/emitResidualTvConstraint"
    --   $ vcat [ ppr (binderVars skol_tvs), ppr wanted ]
    -- setSrcSpan (combineSrcSpans (getLocA bndr_1) (getLocA bndr_n))
    --   $ emitResidualTvConstraint skol_info (binderVars skol_tvs) tclvl wanted
    -- return (skol_tvs, res)

bindExplicitBndrsX :: SkolemMode -> [LCsTyVarBndr Rn] -> TcM a -> TcM ([TcTyVarBinder], a)
bindExplicitBndrsX skol_mode@(SM { sm_kind = ctxt_kind }) cs_tvs thing_inside = do
  traceTc "bindExplicitBndrs" (ppr cs_tvs)
  go cs_tvs
  where
    go [] = do
      res <- thing_inside
      return ([], res)
    go (L _ cs_tv : cs_tvs) = do
      lcl_env <- getLclTyKiEnv
      (tv, flag) <- tc_cs_bndr lcl_env cs_tv
      (tvs, res) <- tcExtendNameTyVarEnv [(csTyVarName cs_tv, toAnyTyVar tv)]
                    $ go cs_tvs
      return (Bndr tv flag : tvs, res)

    tc_cs_bndr lcl_env bndr
      = let (name, lcs_kind, flag) = case bndr of
              KindedTyVar _ (L _ name) kind -> (name, kind, Required)
              ImpKindedTyVar _ (L _ name) kind -> (name, kind, Specified)
        in do kind <- tcLCsKindSig (TyVarBndrKindCtxt name) lcs_kind
              tv <- newTyVarBndr skol_mode name kind
              return (tv, flag)

newTyVarBndr :: SkolemMode -> Name -> AnyMonoKind -> TcM (TcTyVar AnyKiVar)
newTyVarBndr (SM { sm_clone = clone, sm_var = var }) name kind = do
  name <- if clone
          then do uniq <- newUnique
                  return $ setNameUnique name uniq
          else return name
  details <- case var of
               SMDVarVar -> newMetaDetails VarVar
               SMDSkolemVar skol_info -> do
                 lvl <- getTcLevel
                 return $ SkolemVar skol_info lvl
  return $ mkTcTyVar name kind details

--------------------------------------
--           SkolemMode
--------------------------------------
  
data SkolemMode = SM
  { sm_clone :: Bool
  , sm_var :: SkolemModeDetails
  , sm_kind :: ContextKind
  }

data SkolemModeDetails
  = SMDVarVar
  | SMDSkolemVar SkolemInfo

smVanilla :: HasCallStack => SkolemMode
smVanilla = SM { sm_clone = panic "sm_clone"
               , sm_var = pprPanic "sm_var" callStackDoc
               , sm_kind = AnyMonoKind }

--------------------------------------
--    Implicit kind var binders
--------------------------------------

tcImplicitKiBndrs :: SkolemInfo -> [Name] -> TcM a -> TcM ([TcKiVar], a)
tcImplicitKiBndrs skol_info
  = tcImplicitKiBndrsX (smVanilla { sm_clone = False
                                  , sm_var = SMDSkolemVar skol_info })
                       skol_info

tcImplicitKiBndrsX :: SkolemMode -> SkolemInfo -> [Name] -> TcM a -> TcM ([TcKiVar], a)
tcImplicitKiBndrsX skol_mode skol_info kv_nms thing_inside
  | null kv_nms
  = do res <- thing_inside
       return ([], res)
  | otherwise
  = do (tclvl, wanted, (skol_kvs, res)) <- pushLevelAndCaptureConstraints
                                           $ bindImplicitKBndrsX skol_mode kv_nms
                                           $ thing_inside
       wanted <- onlyWantedKiConstraints wanted
       emitResidualKvConstraint skol_info skol_kvs tclvl wanted
       return (skol_kvs, res)

newKiVarBndr :: SkolemMode -> Name -> TcM TcKiVar
newKiVarBndr (SM { sm_clone = clone, sm_var = var }) name = do
  name <- case clone of
            True -> do uniq <- newUnique
                       return $ setNameUnique name uniq
            False -> return name
  details <- case var of
               SMDVarVar -> newMetaDetails VarVar
               SMDSkolemVar skol_info -> do
                 lvl <- getTcLevel
                 return $ SkolemVar skol_info lvl
  return $ mkTcKiVar name details

bindTyConKiVars :: Name -> ([AnyKiVar] -> AnyMonoKind -> Arity -> TcM a) -> TcM a
bindTyConKiVars tycon_name thing_inside = do
  tycon <- tcLookupTcTyCon tycon_name
  let full_kind = tyConKind tycon
      (binders, mono_kind) = splitForAllKiVars full_kind
      arity = tyConArity tycon
  traceTc "bindTyConKiVars" (ppr tycon_name $$ ppr binders $$ ppr mono_kind $$ ppr full_kind)
  tcExtendKiVarEnv binders
    $ thing_inside binders mono_kind arity

bindImplicitKBndrs_Q_Kv :: [Name] -> TcM a -> TcM ([TcKiVar], a)
bindImplicitKBndrs_Q_Kv = bindImplicitKBndrsX (smVanilla { sm_clone = False
                                                         , sm_var = SMDVarVar })

bindImplicitKBndrs_Q_Skol :: SkolemInfo -> [Name] -> TcM a -> TcM ([TcKiVar], a)
bindImplicitKBndrs_Q_Skol skol_info
  = bindImplicitKBndrsX (smVanilla { sm_clone = False
                                   , sm_var = SMDSkolemVar skol_info })

bindImplicitKBndrsX :: SkolemMode -> [Name] -> TcM a -> TcM ([TcKiVar], a)
bindImplicitKBndrsX skol_mode kv_names thing_inside = do
  lcl_env <- getLclTyKiEnv
  kvs <- mapM (new_kv lcl_env) kv_names
  traceTc "bindImplicitKBndrsX" (ppr kv_names $$ ppr kvs)
  res <- tcExtendNameKiVarEnv (kv_names `zip` fmap toAnyKiVar kvs) thing_inside
  return (kvs, res)
  where
    new_kv lcl_env name = newKiVarBndr skol_mode name      

{- *********************************************************************
*                                                                      *
             Kind generalization
*                                                                      *
********************************************************************* -}

kindGeneralizeSome :: SkolemInfo -> WantedKiConstraints -> AnyType -> TcM [TcKiVar]
kindGeneralizeSome skol_info wanted ty = do
  kvs <- candidateQKiVarsOfType ty
  filtered_kvs <- filterConstrainedCandidates wanted kvs
  traceTc "kindGeneralizeSome"
    $ vcat [ text "type:" <+> ppr ty
           , text "kvs:" <+> ppr kvs
           , text "filtered_kvs:" <+> ppr filtered_kvs ]
  quantifyKiVars skol_info filtered_kvs

filterConstrainedCandidates
  :: WantedKiConstraints
  -> DTcKiVarSet
  -> TcM DTcKiVarSet
filterConstrainedCandidates wanted kvs
  | isEmptyWC wanted
  = return kvs
  | otherwise
  = do wc_kvs <- liftZonkM $ zonkAnyKiVarsAndFV $ varsOfWKC wanted
       let (to_promote, kvs') = first dVarSetToVarSet
                                $ partitionDVarSet ((`elemVarSet` wc_kvs) . toAnyKiVar) kvs
       traceTc "filterConstrainedCandidates"
         $ vcat [ text "kvs:" <+> ppr kvs
                , text "wc_kvs:" <+> ppr wc_kvs
                , text "to_promote:" <+> ppr to_promote
                , text "kvs':" <+> ppr kvs' ]
       _ <- promoteKiVarSet to_promote
       return kvs'

typeKindGeneralizeNone :: AnyType -> TcM ()
typeKindGeneralizeNone ty = do
  traceTc "typeKindGeneralizeNone" (ppr ty)
  kvs <- candidateQKiVarsOfType ty
  traceTc "typeKindGeneralizeNone" (ppr ty $$ ppr kvs)
  _ <- promoteKiVarSet $ dVarSetToVarSet kvs
  return ()

kindGeneralizeNone :: AnyMonoKind -> TcM ()
kindGeneralizeNone kind = do
  traceTc "kindGeneralizeNone" (ppr kind)
  dvs <- candidateQKiVarsOfKind (Mono kind)
  _ <- promoteKiVarSet $ dVarSetToVarSet dvs
  return ()

kindGeneralizeNone' :: AnyKind -> TcM ()
kindGeneralizeNone' kind = do
  traceTc "kindGeneralizeNone'" (ppr kind)
  dvs <- candidateQKiVarsOfKind kind
  _ <- promoteKiVarSet $ dVarSetToVarSet dvs
  return ()

{- Note
GHC has to do this since GHC allows user written kind signatures
for top level declarations. E.g., in the declaration of a data/newtype/class
(which happens more often using GADT syntax).
We do things differently, and essentially don't have syntax that would introduce
this issue, nor do we plan to add such syntax.
However, for the sake of future proofing things, we include some sanity checks here.
If we add some syntax that would require the compiler to eta expand,
we should detect it here.
-}
-- etaExpandAlgTyCon
--   :: TyConFlavor tc
--   -> SkolemInfo
--   -> [TcTyConBinder]
--   -> Kind
--   -> TcM ()
-- etaExpandAlgTyCon flav skol_info tcbs res_kind
--   | needsEtaExpansion flav
--   = checkNeedsEtaKind res_kind
--   | otherwise
--   = return ()

needsEtaExpansion :: TyConFlavor -> Bool
needsEtaExpansion DataTypeFlavor = True
needsEtaExpansion TupleFlavor = True
needsEtaExpansion SumFlavor = True
needsEtaExpansion AbstractTypeFlavor = True
needsEtaExpansion TypeFunFlavor = True
needsEtaExpansion BuiltInTypeFlavor = True

checkNeedsEtaKind :: AnyKind -> TcM ()
checkNeedsEtaKind res_kind = case splitFunKi_maybe res_kind of
  Nothing -> return ()
  Just _ -> pprPanic "checkNeedsEtaKind" (ppr res_kind)

{- *********************************************************************
*                                                                      *
      Pattern signatures (i.e signatures that occur in patterns)
*                                                                      *
********************************************************************* -}

tcCsPatSigType :: UserTypeCtxt -> CsPatSigType Rn -> ContextKind -> TcM AnyType
tcCsPatSigType ctxt (CsPS { csps_ext = CsPSRn { csps_imp_kvs = sig_ns }
                          , csps_body = cs_ty }) ctxt_kind
  = tc_type_in_pat ctxt cs_ty sig_ns ctxt_kind

tcCsTyPat
  :: CsTyPat Rn
  -> AnyMonoKind
  -> TcM ([(Name, AnyTyVar AnyKiVar)], [(Name, AnyKiVar)], AnyType)
tcCsTyPat cs_pat@(CsTP { cstp_ext = cstp_rn, cstp_body = cs_ty }) expected_kind
  = case tyPatToBndr cs_pat of
      Nothing -> panic "should always be Just for now"
      Just bndr -> tc_bndr_in_pat bndr imp_kv_ns expected_kind
  where
    CsTPRn { cstp_imp_kvs = imp_kv_ns } = cstp_rn

tc_bndr_in_pat
  :: CsTyVarPatBndr
  -> [Name]
  -> AnyMonoKind
  -> TcM ([(Name, AnyTyVar AnyKiVar)], [(Name, AnyKiVar)], AnyType)
tc_bndr_in_pat bndr imp_kv_ns expected_kind = do
  let CsTvb bvar bkind = bndr
  traceTc "tc_bndr_in_pat 1" (ppr expected_kind)
  name <- tcCsBndrTyVarName bvar
  tv <- toAnyTyVar <$> newPatTyVar name expected_kind
  case bkind of
    CsBndrNoKind -> pure (mk_tvb_pairs bndr tv, [], mkTyVarTy $ toAnyTyVar tv)
    CsBndrKind ki -> do
      kv_prs <- mapM new_implicit_kv imp_kv_ns
      addKindCtxt ki
        $ solveKindCoercions "tc_bndr_in_pat"
        $ tcExtendNameKiVarEnv kv_prs
        $ tcCsTvbKind bvar ki expected_kind
      traceTc " tc_bndr_in_pat 2"
        $ vcat [ text "expected_kind" <+> ppr expected_kind
               , text "(name, tv)" <+> ppr (name, tv)
               , text "kv_prs" <+> ppr kv_prs 
               ]
      pure (mk_tvb_pairs bndr tv, kv_prs, mkTyVarTy $ toAnyTyVar tv)
  where
    new_implicit_kv name = do
      kv <- newPatKiVar name
      return (name, toAnyKiVar kv)

tcCsBndrTyVarName :: CsBndrTyVar -> TcM Name
tcCsBndrTyVarName (CsBndrVar name) = return name
tcCsBndrTyVarName CsBndrWildCard = newSysName (mkTyVarOcc "_")
 
tcCsTvbKind :: CsBndrTyVar -> LCsKind Rn -> AnyMonoKind -> TcM ()
tcCsTvbKind bvar kind expected_kind = do
  sig_kind <- tcLCsKindSig ctxt kind
  traceTc "tcCsTvbKind:unifying" (ppr sig_kind $$ ppr expected_kind)
  discardResult $ unifyKind mb_thing EQKi sig_kind expected_kind
  where
    (ctxt, mb_thing) = case bvar of
      CsBndrVar cs_nm -> (TyVarBndrKindCtxt cs_nm, Just (KiNameThing cs_nm))
      CsBndrWildCard -> (KindSigCtxt, Nothing)

tc_type_in_pat
  :: UserTypeCtxt
  -> LCsType Rn
  -> [Name]
  -> ContextKind
  -> TcM AnyType
tc_type_in_pat ctxt cs_ty ns ctxt_kind = addSigCtxt ctxt cs_ty $ do
  kv_prs <- mapM new_implicit_kv ns
  ty <- addTypeCtxt cs_ty
        $ solveKindCoercions "tc_type_in_pat"
        $ tcExtendNameKiVarEnv kv_prs
        $ do ek <- newExpectedKind ctxt_kind
             tcLCsType cs_ty ek

  typeKindGeneralizeNone ty
  ty <- liftZonkM $ zonkTcType ty
  checkValidType ctxt ty

  traceTc "tc_type_in_pat" (ppr kv_prs)
  return ty
  where
    new_implicit_kv name = do
      kv <- newPatKiVar name
      return (name, toAnyKiVar kv)

tyPatToBndr :: CsTyPat Rn -> Maybe CsTyVarPatBndr 
tyPatToBndr CsTP { cstp_body = L _ cs_ty } = go cs_ty
  where
    go :: CsType Rn -> Maybe CsTyVarPatBndr 
    go (CsParTy _ (L _ ty)) = go ty
    go (CsKindSig _ (L _ ty) ki) = do
      bvar <- go_bvar ty
      let bkind = CsBndrKind ki
      Just $ CsTvb bvar bkind
    go ty = do
      bvar <- go_bvar ty
      Just $ CsTvb bvar CsBndrNoKind

    go_bvar :: CsType Rn -> Maybe CsBndrTyVar
    go_bvar (CsTyVar _ name)
      | isTyVarName (unLoc name)
      = Just $ CsBndrVar $ unLoc name
    go_bvar (CsUnboundTyVar {})
      = Just CsBndrWildCard
    go_bvar _ = Nothing

data CsTyVarPatBndr
  = CsTvb { tvb_var :: CsBndrTyVar
          , tvb_kind :: CsBndrKind }

mk_tvb_pairs :: CsTyVarPatBndr -> AnyTyVar AnyKiVar -> [(Name, AnyTyVar AnyKiVar)]
mk_tvb_pairs (CsTvb bvar _) tv = case bvar of
  CsBndrVar name -> [(name, tv)]
  CsBndrWildCard -> []

data CsBndrTyVar
  = CsBndrVar Name
  | CsBndrWildCard

data CsBndrKind
  = CsBndrKind (LCsKind Rn)
  | CsBndrNoKind

{- *********************************************************************
*                                                                      *
                Sort checking kinds
*                                                                      *
********************************************************************* -}

tcLCsKindSig :: UserTypeCtxt -> LCsKind Rn -> TcM AnyMonoKind
tcLCsKindSig ctxt cs_kind = do
  kind <- addErrCtxt (text "In the kind" <+> quotes (ppr cs_kind))
          $ tcLCsKind cs_kind
  traceTc "tcLCsKindSig" (ppr cs_kind $$ ppr kind)

  kindGeneralizeNone kind
  kind <- liftZonkM $ zonkTcMonoKind kind

  checkValidMonoKind ctxt kind
  traceTc "tcLCsKindSig2" (ppr kind)
  return kind

tcLCsContext :: LCsContext Rn -> TcM ([KiCoVar AnyKiVar], [AnyMonoKind])
tcLCsContext = tcCsContext . unLoc

tcCsContext :: CsContext Rn -> TcM ([KiCoVar AnyKiVar], [AnyMonoKind])
tcCsContext [] = panic "tcCsContext empty"
tcCsContext ctxt = do
  rels <- mapM tc_lcs_kdrel ctxt 
  coVars <- newKiCoVars rels
  return $ (coVars, rels)

tc_lcs_kdrel :: LCsKdRel Rn -> TcM AnyMonoKind
tc_lcs_kdrel rel = tc_cs_kdrel (unLoc rel)

tc_cs_kdrel :: CsKdRel Rn -> TcM AnyMonoKind
tc_cs_kdrel (CsKdLT _ k1 k2) = do
  k1' <- tcLCsKind k1
  k2' <- tcLCsKind k2
  return $ mkKiPredApp LTKi k1' k2'
tc_cs_kdrel (CsKdLTEQ _ k1 k2) = do
  k1' <- tcLCsKind k1
  k2' <- tcLCsKind k2
  return $ mkKiPredApp LTEQKi k1' k2'

{- *********************************************************************
*                                                                      *
             Error messages
*                                                                      *
********************************************************************* -}

funAppCtxt :: (Outputable fun, Outputable arg) => fun -> arg -> Int -> SDoc
funAppCtxt fun arg arg_no = hang (hsep [ text "In the", speakNth arg_no, text "argument of"
                                       , quotes (ppr fun) <> text ", namely" ])
                            2 (quotes (ppr arg))

tupAppCtxt :: Outputable arg => arg -> Int -> SDoc
tupAppCtxt arg arg_no = hang (hsep [ text "In the", speakNth arg_no, text "argument of a tuple type, namely" ])
                             2 (quotes (ppr arg))

addTyConFlavCtxt :: Name -> TyConFlavor -> TcM a -> TcM a
addTyConFlavCtxt name flav
  = addErrCtxt $ hsep [ text "In the", ppr flav
                      , text "declaration for"
                      , quotes (ppr name) ]
