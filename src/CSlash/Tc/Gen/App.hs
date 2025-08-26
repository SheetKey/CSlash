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
           , text "rn_args:" <+> ppr rn_args ]

  (tc_fun, fun_sigma) <- tcInferAppHead fun
  let tc_head = (tc_fun, fun_ctxt)

  (inst_args, app_res_rho) <- setTcLevel QLInstVar
                              $ tcInstFun True tc_head fun_sigma rn_args

  traceTc "tcApp:DoQL" (ppr rn_fun $$ ppr app_res_rho)

  quickLookResultType app_res_rho exp_res_ty

  tc_args <- tcValArgs inst_args

  app_res_rho <- liftZonkM $ zonkTcType app_res_rho

  res_wrap <- checkResultTy rn_expr tc_head inst_args app_res_rho exp_res_ty

  finishApp tc_head tc_args app_res_rho res_wrap

quickLookResultType :: AnyRhoType -> ExpRhoType -> TcM () 
quickLookResultType app_res_rho (Check exp_rho) = qlUnify app_res_rho exp_rho
quickLookResultType _ _ = return ()

finishApp
  :: (CsExpr Tc, AppCtxt)
  -> [CsExprArg 'TcpTc]
  -> AnyRhoType
  -> CsWrapper
  -> TcM (CsExpr Tc)
finishApp tc_head@(tc_fun, _) tc_args app_res_rho res_wrap = do
  let res_expr = rebuildCsApps tc_head tc_args
  return $ mkCsWrap res_wrap res_expr

checkResultTy
  :: CsExpr Rn
  -> (CsExpr Tc, AppCtxt)
  -> [CsExprArg p]
  -> AnyRhoType
  -> ExpRhoType
  -> TcM CsWrapper
checkResultTy _ _ _ app_res_rho (Infer inf_res) = panic "checkResultTy Infer"

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
tcValArg (EWrap {}) = panic "tcValArg EWrap"

tcValArg (EValArg { ea_ctxt = ctxt
                  , ea_arg = larg@(L arg_loc arg)
                  , ea_arg_ty = arg_ty })
  = addArgCtxt ctxt larg $ do
    traceTc "tcValArg"
      $ vcat [ ppr ctxt
             , text "arg type:" <+> ppr arg_ty
             , text "arg:" <+> ppr arg ]

    exp_arg_ty <- liftZonkM $ zonkTcType arg_ty

    arg' <- tcScalingUsage (panic "tcValArg Mult") $ tcPolyExpr arg (mkCheckExpType exp_arg_ty)

    return (EValArg { ea_ctxt = ctxt
                    , ea_arg = L arg_loc arg'
                    , ea_arg_ty = noExtField })

{- *********************************************************************
*                                                                      *
              Instantiating the call
*                                                                      *
********************************************************************* -}

tcInstFun
  :: Bool
  -> (CsExpr Tc, AppCtxt)
  -> AnySigmaType
  -> [CsExprArg 'TcpRn]
  -> TcM ([CsExprArg 'TcpInst], AnySigmaType)
tcInstFun inst_final (tc_fun, fun_ctxt) fun_sigma rn_args = do
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

    inst_fun (EValArg {} : _) = isInvisibleForAllFlag
    inst_fun _ = const False

    go :: Int
       -> [CsExprArg 'TcpInst]
       -> AnySigmaType
       -> [CsExprArg 'TcpRn]
       -> TcM ([CsExprArg 'TcpInst], AnySigmaType)
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
       -> AnySigmaType
       -> [CsExprArg 'TcpRn]
       -> TcM ([CsExprArg 'TcpInst], AnySigmaType)
    go1 pos acc fun_ty (arg : rest_args)
      | fun_is_out_of_scope, looks_like_type_arg arg
      = go pos acc fun_ty rest_args

    go1 pos acc fun_ty args
      | (tvs, body1) <- tcSplitSomeForAllTyVars (inst_fun args) fun_ty
      , not (null tvs)
      = do (_, wrap, fun_rho) <- addHeadCtxt fun_ctxt
                                 $ instantiateSigma fun_orig tvs body1
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

    go1 pos acc fun_ty args@(EValArg {} : _)
      | Just kappa <- getTcTyVar_maybe fun_ty
      , isQLInstVar kappa
      = do arg_tys <- mapM (const $ asAnyTyKi <$> newOpenFlexiTyVarTy) (leadingValArgs args)
           fun_kis <- mapM (const $ asAnyKi <$> newFlexiKiVarKi) (leadingValArgs args)
           res_ty <- asAnyTyKi <$> newOpenFlexiTyVarTy
           let fun_ty' = mkFunTys arg_tys fun_kis res_ty

           kind_co <- unifyKind Nothing EQKi (head fun_kis) (varKind kappa)
           liftZonkM (writeMetaTyVar kappa (mkCastTy fun_ty' kind_co))

           let co_wrap = mkWpCast (mkGReflLeftCo fun_ty' kind_co)
               acc' = addArgWrap co_wrap acc

           go pos acc' fun_ty' args

    go1 pos acc fun_ty (EValArg { ea_arg = arg, ea_ctxt = ctxt } : rest_args) = do
      let herald = case fun_ctxt of
                     VACall{} -> ExpectedFunTyArg (CsExprTcThing tc_fun) (unLoc arg)
      (wrap, arg_ty, res_ty) <- matchActualFunTy herald (Just $ CsExprTcThing tc_fun)
                                                 (n_val_args, fun_sigma) fun_ty
      arg' <- quickLookArg ctxt arg arg_ty
      let acc' = arg' : addArgWrap wrap acc
      go (pos + 1) acc' res_ty rest_args

looks_like_type_arg :: CsExprArg 'TcpRn -> Bool
looks_like_type_arg = panic "looks_like_type_arg"

addArgCtxt :: AppCtxt -> LCsExpr Rn -> TcM a -> TcM a
addArgCtxt = panic "addArgCtxt"

{- *********************************************************************
*                                                                      *
              Visible type application
*                                                                      *
********************************************************************* -}

tcVDQ :: (AnyTyVarBinder, AnyType) -> LCsExpr Rn -> TcM (AnyType, AnyType)
tcVDQ = panic "tcVDQ"

{- *********************************************************************
*                                                                      *
              Quick Look
*                                                                      *
********************************************************************* -}

quickLookArg :: AppCtxt -> LCsExpr Rn -> AnySigmaType -> TcM (CsExprArg 'TcpInst)
quickLookArg = panic "quickLookArg"

{- *********************************************************************
*                                                                      *
                 QuickLook unification
*                                                                      *
********************************************************************* -}

qlUnify :: AnyType -> AnyType -> TcM ()
qlUnify ty1 ty2 = do
  traceTc "qlUnify" (ppr ty1 $$ ppr ty2)
  go ty1 ty2
  where
    go :: AnyType -> AnyType -> TcM ()

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

    go _ _ = return ()

    go_kappa kappa ty2 = assertPpr (isMetaVar kappa) (ppr kappa) $ do
      cts <- readMetaTyVar kappa
      case cts of
        Indirect ty1 -> go ty1 ty2
        Flexi -> do ty2 <- liftZonkM $ zonkTcType ty2
                    go_flexi kappa ty2

    go_flexi mkappa (TyVarTy tv2)
      | let kappa = toAnyTyVar mkappa
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
