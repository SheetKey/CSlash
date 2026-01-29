{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}

module CSlash.Tc.Gen.App where

import {-# SOURCE #-} CSlash.Tc.Gen.Expr( tcPolyExpr )

import CSlash.Cs

import CSlash.Tc.Gen.Head
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Utils.Unify
import CSlash.Tc.Utils.Instantiate
import CSlash.Tc.Gen.CsType
import CSlash.Tc.Utils.TcMType
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Types.Origin
import CSlash.Tc.Utils.TcType as TcType
import CSlash.Tc.Zonk.TcType

import CSlash.Core.ConLike (ConLike(..))
import CSlash.Core.DataCon ( dataConTyCon )
import CSlash.Core.TyCon
import CSlash.Core.Kind
import CSlash.Core.Type.Rep
import CSlash.Core.Type.Ppr
-- import CSlash.Core.Type.Subst ( substTyWithInScope )
import CSlash.Core.Type
-- import GHC.Core.Coercion

import CSlash.Builtin.Names

import CSlash.Types.Var
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Name.Reader
import CSlash.Types.SrcLoc
import CSlash.Types.Var.Env  ( emptyTidyEnv, mkInScopeSet )

import CSlash.Data.Maybe

import CSlash.Utils.Misc
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic

import Control.Monad
import Data.Function
import Data.Semigroup

{- *********************************************************************
*                                                                      *
              Typechecking n-ary applications
*                                                                      *
********************************************************************* -}

tcApp :: CsExpr Rn -> ExpRhoType -> TcM (CsExpr Tc)
tcApp rn_expr exp_res_ty = do
  (fun@(rn_fun, fun_ctxt), rn_args) <- splitCsApps rn_expr
  traceTc "tcApp {"
    $ vcat [ text "rn_expr:" <+> ppr rn_expr
           , text "rn_fun:" <+> ppr rn_fun
           , text "fun_ctxt:" <+> ppr fun_ctxt
           , text "rn_args:" <+> ppr rn_args
           , text "exp_res_ty:" <+> ppr exp_res_ty ]

  (tc_fun, fun_sigma) <- tcInferAppHead fun
  let tc_head = (tc_fun, fun_ctxt)

  (inst_args, app_res_rho) <- setTcLevel QLInstVar
                              $ tcInstFun tc_head fun_sigma rn_args

  traceTc "tcApp:DoQL" (ppr rn_fun $$ ppr app_res_rho)

  quickLookResultType app_res_rho exp_res_ty

  tc_args <- tcValArgs inst_args

  app_res_rho <- liftZonkM $ zonkTcType app_res_rho

  traceTc "tcApp:checkResultTy"
    $ vcat [ text "zonked app_res_rho:" <+> ppr app_res_rho ]
  res_wrap <- checkResultTy rn_expr tc_head inst_args app_res_rho exp_res_ty

  finishApp tc_head tc_args app_res_rho res_wrap

quickLookResultType :: RhoType Tc -> ExpRhoType -> TcM () 
quickLookResultType app_res_rho (Check exp_rho) = qlUnify app_res_rho exp_rho
quickLookResultType _ _ = return ()

finishApp
  :: (CsExpr Tc, AppCtxt)
  -> [CsExprArg 'TcpTc]
  -> RhoType Tc
  -> CsWrapper Tc
  -> TcM (CsExpr Tc)
finishApp tc_head@(tc_fun, _) tc_args app_res_rho res_wrap = do
  let res_expr = rebuildCsApps tc_head tc_args
  return $ mkCsWrap res_wrap res_expr

checkResultTy
  :: CsExpr Rn
  -> (CsExpr Tc, AppCtxt)
  -> [CsExprArg p]
  -> RhoType Tc
  -> ExpRhoType
  -> TcM (CsWrapper Tc)
checkResultTy _ _ _ app_res_rho (Infer inf_res) = do
  co <- fillInferResult app_res_rho inf_res
  return $ mkWpCast co

checkResultTy rn_expr (tc_fun, fun_ctxt) inst_args app_res_rho (Check res_ty) =
  perhaps_add_res_ty_ctxt $ do
  traceTc "checkResultTy {"
    $ vcat [ text "tc_fun:" <+> ppr tc_fun
           , text "app_res_rho:" <+> ppr app_res_rho
           , text "res_ty:" <+> ppr res_ty ]
  co <- unifyExprType rn_expr app_res_rho res_ty
  traceTc "checkResultTy 1 }" (ppr co)
  return (mkWpCast co)
  where
    perhaps_add_res_ty_ctxt thing_inside
      | insideExpansion fun_ctxt
      = addHeadCtxt fun_ctxt thing_inside
      | otherwise
      = addFunResCtxt tc_fun inst_args app_res_rho (mkCheckExpType res_ty) $ thing_inside

tcValArgs :: [CsExprArg 'TcpInst] -> TcM [CsExprArg 'TcpTc]
tcValArgs = mapM tcValArg

tcValArg :: CsExprArg 'TcpInst -> TcM (CsExprArg 'TcpTc)
tcValArg (ETypeArg l loc cs_ty ty) = return (ETypeArg l loc cs_ty ty)
tcValArg (EWrap ew) = return $ EWrap ew

tcValArg (EValArg { ea_ctxt = ctxt
                  , ea_arg = larg@(L arg_loc arg)
                  , ea_arg_ty = arg_ty })
  = addArgCtxt ctxt larg $ do
    traceTc "tcValArg"
      $ vcat [ ppr ctxt
             , text "arg type:" <+> ppr arg_ty
             , text "arg:" <+> ppr arg ]

    exp_arg_ty <- liftZonkM $ zonkTcType arg_ty

    arg' <- {-tcScalingUsage (panic "tcValArg Mult") $-} tcPolyExpr arg (mkCheckExpType exp_arg_ty)

    return (EValArg { ea_ctxt = ctxt
                    , ea_arg = L arg_loc arg'
                    , ea_arg_ty = noExtField })

tcValArg (EValArgQL { eaql_wanted = wanted
                    , eaql_ctxt = ctxt
                    , eaql_arg_ty = arg_ty
                    , eaql_larg = larg@(L arg_loc rn_expr)
                    , eaql_tc_fun = tc_head
                    , eaql_fun_ue = head_ue
                    , eaql_args = inst_args
                    , eaql_encl = arg_influences_enclosing_call
                    , eaql_res_rho = app_res_rho })
  = addArgCtxt ctxt larg $ do
  exp_arg_ty <- liftZonkM $ zonkTcType arg_ty
  traceTc "tcEValArgQL {"
    $ vcat [ text "app_res_rho:" <+> ppr app_res_rho
           , text "exp_arg_ty:" <+> ppr exp_arg_ty
           , text "args:" <+> ppr inst_args ]

  (wrap, arg') <- {-tcScalingUsage (panic "tcValArg Mult")
                  $ -}tcSkolemize GenSigCtxt exp_arg_ty $ \ exp_arg_rho -> do
                    emitConstraints wanted
                    tcEmitBindingUsage head_ue
                    unless arg_influences_enclosing_call
                      $ qlUnify app_res_rho exp_arg_rho
                    tc_args <- tcValArgs inst_args
                    app_res_rho <- liftZonkM $ zonkTcType app_res_rho
                    traceTc "tcValArg:checkResultTy" empty
                    res_wrap <- checkResultTy rn_expr tc_head inst_args app_res_rho
                                              (mkCheckExpType exp_arg_rho)
                    finishApp tc_head tc_args app_res_rho res_wrap
  traceTc "tcEValArgQL }"
    $ vcat [ text "app_res_rho:" <+> ppr app_res_rho ]

  return $ EValArg { ea_ctxt = ctxt
                   , ea_arg = L arg_loc (mkCsWrap wrap arg')
                   , ea_arg_ty = noExtField }

{- *********************************************************************
*                                                                      *
              Instantiating the call
*                                                                      *
********************************************************************* -}

tcInstFun
  :: (CsExpr Tc, AppCtxt)
  -> SigmaType Tc
  -> [CsExprArg 'TcpRn]
  -> TcM ([CsExprArg 'TcpInst], SigmaType Tc)
tcInstFun (tc_fun, fun_ctxt) fun_sigma rn_args = do
  traceTc "tcInstFun"
    $ vcat [ text "tc_fun" <+> ppr tc_fun
           , text "fun_sigma" <+> ppr fun_sigma
           , text "fun_ctxt" <+> ppr fun_ctxt
           , text "args:" <+> ppr rn_args ]
  go 1 [] fun_sigma rn_args
  where
    fun_orig = case fun_ctxt of
      VACall e _ _ -> exprCtOrigin e

    n_val_args = count isCsValArg rn_args
    
    fun_is_out_of_scope = case tc_fun of
                            CsUnboundVar {} -> True
                            _ -> False

    inst_fun :: [CsExprArg 'TcpRn] -> ForAllFlag -> Bool
    inst_fun [] = isInvisibleForAllFlag
    inst_fun (EValArg {} : _) = isInvisibleForAllFlag
    inst_fun _ = const False

    go :: Int
       -> [CsExprArg 'TcpInst]
       -> SigmaType Tc
       -> [CsExprArg 'TcpRn]
       -> TcM ([CsExprArg 'TcpInst], SigmaType Tc)
    go pos acc fun_ty args
      | Just kappa <- getTcTyVar_maybe fun_ty
      , isQLInstVar kappa
      = do cts <- readMetaTyVar kappa
           case cts of
             Indirect fun_ty' -> go pos acc fun_ty' args
             Flexi -> go1 pos acc fun_ty args
      | otherwise
      = go1 pos acc fun_ty args

    go1 :: Int
       -> [CsExprArg 'TcpInst]
       -> SigmaType Tc
       -> [CsExprArg 'TcpRn]
       -> TcM ([CsExprArg 'TcpInst], SigmaType Tc)
    go1 pos acc fun_ty (arg : rest_args)
      | fun_is_out_of_scope, looks_like_type_arg arg
      = go pos acc fun_ty rest_args

    go1 pos acc fun_ty args
      | (kvs, body1) <- tcSplitBigLamKiVars fun_ty
      , (tvs, body2) <- tcSplitSomeForAllTyVars (inst_fun args) body1
      , not (null kvs && null tvs)
      = do (_, _, wrap, fun_rho) <- addHeadCtxt fun_ctxt
                                 $ instantiateSigma fun_orig kvs tvs body2 fun_ty
           traceTc "go1 instantiateSigma" (ppr fun_rho)
           go pos (addArgWrap wrap acc) fun_rho args

    go1 _ acc fun_ty [] = do
      traceTc "tcInstFun:ret" (ppr fun_ty)
      return (reverse acc, fun_ty)

    go1 pos acc fun_ty ((EValArg { ea_arg = arg }) : rest_args)
      | Just (tvb, body) <- tcSplitForAllTyVarBinder_maybe fun_ty
      = assertPpr (binderFlag tvb == Required) (ppr fun_ty $$ ppr arg) $ do
          (ty_arg, inst_body) <- tcVDQ (tvb, body) arg
          let wrap = mkWpTyApps [ty_arg]
          go (pos + 1) (addArgWrap wrap acc) inst_body rest_args

    go1 pos acc fun_ty (EWrap w : args) = go1 pos (EWrap w : acc) fun_ty args

    go1 pos acc fun_ty (ETypeArg { ea_ctxt = ctxt, ea_loc = loc, ea_cs_ty = cs_ty } : rest_args)
      = do
      (ty_arg, inst_ty) <- tcVTA fun_ty cs_ty
      let arg' = ETypeArg { ea_ctxt = ctxt, ea_loc = loc, ea_cs_ty = cs_ty, ea_ty_arg = ty_arg }
      go pos (arg' : acc) inst_ty rest_args

    go1 pos acc fun_ty args@(EValArg {} : _)
      | Just kappa <- getTcTyVar_maybe fun_ty
      , isQLInstVar kappa
      = do arg_tys <- mapM (const newOpenFlexiTyVarTy) (leadingValArgs args)
           fun_kis <- mapM (const newFlexiKiVarKi) (leadingValArgs args)
           res_ty <- newOpenFlexiTyVarTy
           let fun_ty' = mkFunTys arg_tys fun_kis res_ty

           kind_co <- unifyKind Nothing EQKi (head fun_kis) (varKind kappa)
           liftZonkM (writeMetaTyVar kappa (mkCastTy fun_ty' kind_co))

           let co_wrap = mkWpCast (mkGReflLeftCo fun_ty' kind_co)
               acc' = addArgWrap co_wrap acc

           go pos acc' fun_ty' args

    go1 pos acc fun_ty (EValArg { ea_arg = arg, ea_ctxt = ctxt } : rest_args) = do
      traceTc "go1 last" (ppr fun_ty $$ ppr arg $$ ppr rest_args)
      let herald = case fun_ctxt of
                     VACall{} -> ExpectedFunTyArg (CsExprTcThing tc_fun) (unLoc arg)
      (wrap, arg_ty, res_ty) <- matchActualFunTy herald (Just $ CsExprTcThing tc_fun)
                                                 (n_val_args, fun_sigma) fun_ty
      traceTc "go1 matchActualFunTy" (ppr arg_ty $$ ppr res_ty)
      arg' <- quickLookArg ctxt arg arg_ty
      let acc' = arg' : addArgWrap wrap acc
      go (pos + 1) acc' res_ty rest_args

looks_like_type_arg :: CsExprArg 'TcpRn -> Bool
looks_like_type_arg = panic "looks_like_type_arg"

addArgCtxt :: AppCtxt -> LCsExpr Rn -> TcM a -> TcM a
addArgCtxt ctxt (L arg_loc arg) thing_inside = 
  case ctxt of
    VACall fun arg_no _ -> setSrcSpanA arg_loc
                           $ addErrCtxt (funAppCtxt fun arg arg_no)
                           $ thing_inside

{- *********************************************************************
*                                                                      *
              Visible type application
*                                                                      *
********************************************************************* -}

tcVTA :: Type Tc -> LCsType Rn -> TcM (Type Tc, Type Tc)
tcVTA = panic "tcVTA"

tcVDQ :: (ForAllBinder (TyVar Tc), Type Tc) -> LCsExpr Rn -> TcM (Type Tc, Type Tc)
tcVDQ = panic "tcVDQ"

{- *********************************************************************
*                                                                      *
              Quick Look
*                                                                      *
********************************************************************* -}

quickLookArg :: AppCtxt -> LCsExpr Rn -> SigmaType Tc -> TcM (CsExprArg 'TcpInst)
quickLookArg ctxt larg orig_arg_ty = do
  is_rho <- tcIsDeepRho orig_arg_ty
  traceTc "qla" (ppr orig_arg_ty $$ ppr is_rho)
  if not is_rho
    then skipQuickLook ctxt larg orig_arg_ty
    else quickLookArg1 ctxt larg orig_arg_ty

skipQuickLook :: AppCtxt -> LCsExpr Rn -> RhoType Tc -> TcM (CsExprArg 'TcpInst)
skipQuickLook ctxt larg arg_ty = return $ EValArg { ea_ctxt = ctxt
                                                  , ea_arg = larg
                                                  , ea_arg_ty = arg_ty }

tcIsDeepRho :: Type Tc -> TcM Bool
tcIsDeepRho ty = go ty
  where
    go ty
      | isSigmaTy ty = return False
      | Just kappa <- getTcTyVar_maybe ty
      , isQLInstVar kappa
      = do info <- readMetaTyVar kappa
           case info of
             Indirect arg_ty' -> go arg_ty'
             Flexi -> return True
      | otherwise = return True

isGuardedTy :: Type Tc -> Bool
isGuardedTy ty
  | Just (tc, _) <- tcSplitTyConApp_maybe ty = isGenerativeTyCon tc
  | Just {} <- tcSplitAppTy_maybe ty = True
  | otherwise = False

quickLookArg1 :: AppCtxt -> LCsExpr Rn -> RhoType Tc -> TcM (CsExprArg 'TcpInst)
quickLookArg1 ctxt larg@(L _ arg) orig_arg_rho = addArgCtxt ctxt larg $ do
  ((rn_fun, fun_ctxt), rn_args) <- splitCsApps arg
  (fun_ue, mb_fun_ty) <- tcCollectingUsage $ tcInferAppHead_maybe rn_fun
  traceTc "quickLookArg {"
    $ vcat [ text "arg:" <+> ppr arg
           , text "orig_arg_rho:" <+> ppr orig_arg_rho
           , text "head:" <+> ppr rn_fun <+> colon <+> ppr mb_fun_ty
           , text "args:" <+> ppr rn_args ]

  case mb_fun_ty of
    Nothing -> skipQuickLook ctxt larg orig_arg_rho
    Just (tc_fun, fun_sigma) -> do
      let tc_head = (tc_fun, fun_ctxt)
      ((inst_args, app_res_rho), wanted) <- captureConstraints
        $ tcInstFun tc_head fun_sigma rn_args

      traceTc "quickLookArg2"
        $ vcat [ text "arg:" <+> ppr arg
               , text "orig_arg_rho:" <+> ppr orig_arg_rho
               , text "app_res_rho:" <+> ppr app_res_rho ]

      arg_influences_enclosing_call <- if isGuardedTy orig_arg_rho
                                       then return True
                                       else not <$> anyFreeKappa app_res_rho
      when arg_influences_enclosing_call
        $ qlUnify app_res_rho orig_arg_rho

      traceTc "quickLookArg done }" (ppr rn_fun)

      return $ EValArgQL { eaql_ctxt = ctxt
                         , eaql_arg_ty = orig_arg_rho
                         , eaql_larg = larg
                         , eaql_tc_fun = tc_head
                         , eaql_fun_ue = fun_ue
                         , eaql_args = inst_args
                         , eaql_wanted = wanted
                         , eaql_encl = arg_influences_enclosing_call
                         , eaql_res_rho = app_res_rho }

{- *********************************************************************
*                                                                      *
                 Folding over instantiation variables
*                                                                      *
********************************************************************* -}

anyFreeKappa :: Type Tc -> TcM Bool
anyFreeKappa ty = unTcMBool (foldQLInstVars go_tv ty)
  where
    go_tv tv = TCMB $ do info <- readMetaTyVar tv
                         case info of
                           Indirect ty -> anyFreeKappa ty
                           Flexi -> return True

newtype TcMBool = TCMB { unTcMBool :: TcM Bool }

instance Semigroup TcMBool where
  TCMB ml <> TCMB mr = TCMB $ do l <- ml
                                 if l
                                   then return True
                                   else  mr

instance Monoid TcMBool where
  mempty = TCMB $ return False

foldQLInstVars :: forall a. Monoid a => (TcTyVar -> a) -> Type Tc -> a
{-# INLINE foldQLInstVars #-}
foldQLInstVars check_tv ty = do_ty ty
  where
    (do_ty, _, _, _) = foldTyCo folder ()

    folder :: TyCoFolder Tc () () () a
    folder = TyCoFolder { tcf_view = noView
                        , tcf_tyvar = do_tv
                        , tcf_covar = mempty
                        , tcf_hole = do_hole
                        , tcf_tybinder = \_ _ _ -> ()
                        , tcf_tylambinder = \_ _ -> ()
                        , tcf_tylamkibinder = \_ _ -> ()
                        , tcf_swapEnv = \_ -> ()
                        , tcf_embedKiRes = \_ -> mempty
                        , tcf_mkcf = MKiCoFolder { mkcf_kivar = \_ _ -> ()
                                                 , mkcf_covar = \_ _ -> ()
                                                 , mkcf_hole = \_ _ -> () }
                        }
    do_hole _ hole = do_ty (tyCoVarPred (tyCoHoleCoVar hole))

    do_tv :: () -> TyVar Tc -> a
    do_tv _ tv | Just tctv <- toTcTyVar_maybe tv
               , isQLInstVar tctv = check_tv tctv
               | otherwise = mempty

{- *********************************************************************
*                                                                      *
                 QuickLook unification
*                                                                      *
********************************************************************* -}

qlUnify :: Type Tc -> Type Tc -> TcM ()
qlUnify ty1 ty2 = do
  traceTc "qlUnify" (ppr ty1 $$ ppr ty2)
  go ty1 ty2
  where
    go :: Type Tc -> Type Tc -> TcM ()

    go (TyVarTy tv) ty2
      | Just mtv <- toTcTyVar_maybe tv
      , isMetaVar mtv
      = go_kappa mtv ty2
    go ty1 (TyVarTy tv)
      | Just mtv <- toTcTyVar_maybe tv
      , isMetaVar mtv
      = go_kappa mtv ty1

    go (CastTy ty1 _) ty2 = go ty1 ty2
    go ty1 (CastTy ty2 _) = go ty1 ty2

    go (TyConApp tc1 []) (TyConApp tc2 [])
      | tc1 == tc2
      = return ()

    go rho1 rho2
      | Just rho1 <- coreView rho1 = go rho1 rho2
      | Just rho2 <- coreView rho2 = go rho1 rho2

    go (TyConApp tc1 tys1) (TyConApp tc2 tys2)
      | tc1 == tc2
      , tys1 `equalLength` tys2
      = zipWithM_ go tys1 tys2

    go (FunTy { ft_kind = ki1, ft_arg = arg1, ft_res = res1 })
       (FunTy { ft_kind = ki2, ft_arg = arg2, ft_res = res2 })
      = do go arg1 arg2
           traceTc "qlUnify/FunTy go ki1 ki2" (ppr ki1 $$ ppr ki2)
           go res1 res2

    go (AppTy t1a t1b) ty2
      | Just (t2a, t2b) <- tcSplitAppTyNoView_maybe ty2
      = do go t1a t2a
           go t1b t2b

    go ty1 (AppTy t2a t2b)
      | Just (t1a, t1b) <- tcSplitAppTyNoView_maybe ty2
      = do go t1a t2a
           go t1b t2b

    go (Embed mki1) (Embed mki2) = go_mono_ki mki1 mki2

    go _ _ = return ()

    go_kappa kappa ty2 = assertPpr (isMetaVar kappa) (ppr kappa) $ do
      cts <- readMetaTyVar kappa
      case cts of
        Indirect ty1 -> go ty1 ty2
        Flexi -> do ty2 <- liftZonkM $ zonkTcType ty2
                    go_flexi kappa ty2

    go_flexi mkappa (TyVarTy tv2)
      | let kappa = TcTyVar mkappa
      , lhsTyPriority tv2 > lhsTyPriority kappa
      , Just mtv2 <- toTcTyVar_maybe tv2
      , isMetaVar mtv2
      = go_flexi1 mtv2 (TyVarTy kappa)
    go_flexi kappa ty2 = go_flexi1 kappa ty2

    go_flexi1 kappa ty2
      | simpleUnifyCheckType UC_QuickLook kappa ty2
      = do kco <- unifyKind (Just (TypeThing ty2)) EQKi (typeMonoKind ty2) (varKind kappa)
           let ty2' = mkCastTy ty2 kco
           traceTc "qlUnify:update"
             $ ppr kappa <+> text ":=" <+> ppr ty2
           liftZonkM $ writeMetaTyVar kappa ty2'
      | otherwise
      = return ()

    go_mono_ki :: MonoKind Tc -> MonoKind Tc -> TcM ()
    go_mono_ki (KiVarKi kv) ki2
      | Just mkv <- toTcKiVar_maybe kv
      , isMetaVar mkv
      = go_ki_kappa mkv ki2
    go_mono_ki ki1 (KiVarKi kv)
      | Just mkv <- toTcKiVar_maybe kv
      , isMetaVar mkv
      = go_ki_kappa mkv ki1
    go_mono_ki (BIKi k1) (BIKi k2)
      | k1 == k2
      = return ()
    go_mono_ki (FunKi {}) (FunKi {}) = panic "qlUnify:go_mono_ki:FunKi"
    go_mono_ki _ _ = return ()

    go_ki_kappa kappa ki2 = assertPpr (isMetaVar kappa) (ppr kappa) $ do
      info <- readMetaKiVar kappa
      case info of
        Indirect ki1 -> go_mono_ki ki1 ki2
        Flexi -> do ki2 <- liftZonkM $ zonkTcMonoKind ki2
                    go_ki_flexi kappa ki2

    go_ki_flexi mkappa (KiVarKi kv2)
      | let kappa = TcKiVar mkappa
      , lhsKiPriority kv2 > lhsKiPriority kappa
      , Just mkv2 <- toTcKiVar_maybe kv2
      , isMetaVar mkv2
      = go_ki_flexi1 mkv2 (KiVarKi kappa)
    go_ki_flexi kappa ki2 = go_ki_flexi1 kappa ki2

    go_ki_flexi1 kappa ki2
      | simpleUnifyCheckKind kappa ki2
      = do traceTc "qlUnify:update:ki"
             $ ppr kappa <+> text ":=" <+> ppr ki2
           liftZonkM $ writeMetaKiVar kappa ki2
      | otherwise
      = return ()
