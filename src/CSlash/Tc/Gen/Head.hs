{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}

module CSlash.Tc.Gen.Head where

import Prelude hiding ((<>))

import {-# SOURCE #-} CSlash.Tc.Gen.Expr( tcExpr, tcPolyLExprSig )

import CSlash.Cs
-- import CSlash.Cs.Syn.Type

import CSlash.Tc.Gen.CsType
-- import GHC.Tc.Gen.Bind( chooseInferredQuantifiers )
import CSlash.Tc.Gen.Sig( tcUserTypeSig )
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Utils.Unify
import CSlash.Tc.Utils.Instantiate
import CSlash.Tc.Errors.Types
-- import GHC.Tc.Solver          ( InferMode(..), simplifyInfer )
import CSlash.Tc.Utils.Env
import CSlash.Tc.Utils.TcMType
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.BasicTypes
import CSlash.Tc.Types.Constraint( WantedTyConstraints )
import CSlash.Tc.Utils.TcType as TcType
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Zonk.TcType

import CSlash.Core.UsageEnv      ( singleUsageUE, UsageEnv )
import CSlash.Core.ConLike( ConLike(..) )
import CSlash.Core.DataCon
import CSlash.Core.TyCon
import CSlash.Core.Type.Rep
import CSlash.Core.Type

import CSlash.Types.Id
import CSlash.Types.Var
import CSlash.Types.Id.Info
import CSlash.Types.Name
import CSlash.Types.Name.Reader
import CSlash.Types.SrcLoc
import CSlash.Types.Basic
import CSlash.Types.Error

import CSlash.Builtin.Names

import CSlash.Driver.DynFlags
import CSlash.Utils.Misc
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic

import CSlash.Data.Maybe
import Control.Monad
import CSlash.Rename.Unbound (WhatLooking(WL_Anything))

{- *********************************************************************
*                                                                      *
              HsExprArg: auxiliary data type
*                                                                      *
********************************************************************* -}

data TcPass
  = TcpRn
  | TcpInst
  | TcpTc

data CsExprArg (p :: TcPass) where
  EValArg :: { ea_ctxt :: AppCtxt
             , ea_arg_ty :: !(XEVAType p)
             , ea_arg :: LCsExpr (CsPass (XPass p)) }
          -> CsExprArg p
  EValArgQL :: { eaql_ctxt :: AppCtxt
               , eaql_arg_ty :: AnySigmaType
               , eaql_larg :: LCsExpr Rn
               , eaql_tc_fun :: (CsExpr Tc, AppCtxt)
               , eaql_fun_ue :: UsageEnv
               , eaql_args :: [CsExprArg 'TcpInst]
               , eaql_wanted :: WantedTyConstraints
               , eaql_encl :: Bool
               , eaql_res_rho :: AnyRhoType }
            -> CsExprArg 'TcpInst
  ETypeArg :: { ea_ctxt :: AppCtxt
              , ea_loc :: SrcSpanAnnA
              , ea_cs_ty :: LCsType Rn
              , ea_ty_arg :: !(XETAType p) }
           -> CsExprArg p
  EWrap :: EWrap -> CsExprArg p

type family XEVAType (p :: TcPass) where
  XEVAType 'TcpInst = AnySigmaType
  XEVAType _ = NoExtField

type family XETAType (p :: TcPass) where
  XETAType 'TcpRn = NoExtField
  XETAType _ = AnyType

data EWrap
  = EPar AppCtxt
  | EExpand CsThingRn
  | ECsWrap AnyCsWrapper

data AppCtxt
  = VACall (CsExpr Rn) Int SrcSpan

instance Outputable AppCtxt where
  ppr (VACall f n l) = text "VACall" <+> int n <+> ppr f <+> ppr l

instance OutputableBndrId (XPass p) => Outputable (CsExprArg p) where
  ppr (EValArg { ea_arg = arg, ea_ctxt = ctxt })
    = text "EValArg" <> braces (ppr ctxt) <+> ppr arg
  ppr (EValArgQL { eaql_tc_fun = fun, eaql_args = args, eaql_res_rho = ty })
    = hang (text "EValArgQL" <+> ppr fun)
      2 (vcat [ ppr args, text "eaql_ty:" <+> ppr ty ])
  ppr (ETypeArg { ea_cs_ty = cs_ty }) = braces (ppr cs_ty)
  ppr (EWrap wrap) = ppr wrap

instance Outputable EWrap where
  ppr (EPar _) = text "EPar"
  ppr (ECsWrap w) = text "ECsWrap" <+> ppr w
  ppr (EExpand orig) = text "EExpand" <+> ppr orig

appCtxtLoc :: AppCtxt -> SrcSpan
appCtxtLoc (VACall _ _ l) = l

insideExpansion :: AppCtxt -> Bool
insideExpansion (VACall {}) = False

type family XPass (p :: TcPass) where
  XPass 'TcpRn = 'Renamed
  XPass 'TcpInst = 'Renamed
  XPass 'TcpTc = 'Typechecked

-- Needs to check the 'e':
-- It could be 'Embed'ing a type, in which case it should be ETypeArg!
mkEValArg :: AppCtxt -> LCsExpr Rn -> CsExprArg 'TcpRn
mkEValArg ctxt (L l (CsEmbTy _ ty)) = mkETypeArg ctxt ty l
mkEValArg ctxt e = EValArg { ea_arg = e
                           , ea_ctxt = ctxt
                           , ea_arg_ty = noExtField }

mkETypeArg :: AppCtxt -> LCsType Rn -> SrcSpanAnnA -> CsExprArg 'TcpRn
mkETypeArg ctxt cs_ty l = ETypeArg { ea_ctxt = ctxt
                                   , ea_loc = l
                                   , ea_cs_ty = cs_ty
                                   , ea_ty_arg = noExtField }
 
addArgWrap :: AnyCsWrapper -> [CsExprArg p] -> [CsExprArg p]
addArgWrap wrap args
  | isIdCsWrapper wrap = args
  | otherwise = EWrap (ECsWrap wrap) : args

splitCsApps :: CsExpr Rn -> TcM ((CsExpr Rn, AppCtxt), [CsExprArg 'TcpRn])
splitCsApps e = go e (top_ctxt 0 e) []
  where
    top_ctxt :: Int -> CsExpr Rn -> AppCtxt
    top_ctxt n (CsPar _ fun) = top_lctxt n fun
    top_ctxt n (CsApp _ fun _) = top_lctxt (n+1) fun
    top_ctxt n other_fun = VACall other_fun n noSrcSpan

    top_lctxt n (L _ fun) = top_ctxt n fun

    go
      :: CsExpr Rn
      -> AppCtxt
      -> [CsExprArg 'TcpRn]
      -> TcM ((CsExpr Rn, AppCtxt), [CsExprArg 'TcpRn])
    go (CsPar _ (L l fun)) ctxt args = go fun (set l ctxt) (EWrap (EPar ctxt) : args)
    go (CsApp _ (L l fun) arg) ctxt args = go fun (dec l ctxt) (mkEValArg ctxt arg : args)
    go e@(OpApp _ arg1 (L l op) arg2) _ args
      = pure ( (op, VACall op 0 (locA l))
             ,   mkEValArg (VACall op 1 generatedSrcSpan) arg1
               : mkEValArg (VACall op 2 generatedSrcSpan) arg2
               : EWrap (EExpand (OrigExpr e))
               : args )
    go e ctxt args = pure ((e, ctxt), args)

    set :: EpAnn ann -> AppCtxt -> AppCtxt
    set l (VACall f n _) = VACall f n (locA l)

    dec :: EpAnn ann -> AppCtxt -> AppCtxt
    dec l (VACall f n _) = VACall f (n-1) (locA l)

rebuildCsApps :: (CsExpr Tc, AppCtxt) -> [CsExprArg 'TcpTc] -> CsExpr Tc
rebuildCsApps (fun, _) [] = fun
rebuildCsApps (fun, ctxt) (arg:args) = case arg of
  EValArg { ea_arg = arg, ea_ctxt = ctxt' }
    -> rebuildCsApps (CsApp noExtField lfun arg, ctxt') args
  ETypeArg { ea_cs_ty = cs_ty, ea_ty_arg = ty, ea_ctxt = ctxt', ea_loc = l }
    -> rebuildCsApps (CsApp noExtField lfun (L l (CsEmbTy ty cs_ty)), ctxt') args
  EWrap (EPar ctxt')
    -> rebuildCsApps (gCsPar lfun, ctxt') args
  EWrap (EExpand (OrigExpr oe))
    -> rebuildCsApps (mkExpandedExprTc oe fun, ctxt) args
  EWrap (ECsWrap wrap)
    -> rebuildCsApps (mkCsWrap wrap fun, ctxt) args
  where
    lfun = L (noAnnSrcSpan $ appCtxtLoc' ctxt) fun

    appCtxtLoc' v = appCtxtLoc v

isCsValArg :: CsExprArg id -> Bool
isCsValArg (EValArg {}) = True
isCsValArg _ = False

leadingValArgs :: [CsExprArg 'TcpRn] -> [LCsExpr Rn]
leadingValArgs = panic "leadingValArgs"

isValArg :: CsExprArg id -> Bool
isValArg (EValArg {}) = True
isValArg _ = False

{- *********************************************************************
*                                                                      *
                 tcInferAppHead
*                                                                      *
********************************************************************* -}

tcInferAppHead :: (CsExpr Rn, AppCtxt) -> TcM (CsExpr Tc, AnySigmaType)
tcInferAppHead (fun, ctxt) = addHeadCtxt ctxt $ do
  mb_tc_fun <- tcInferAppHead_maybe fun
  case mb_tc_fun of
    Just (fun', fun_sigma) -> return (fun', fun_sigma)
    Nothing -> tcInfer (tcExpr fun)

tcInferAppHead_maybe :: CsExpr Rn -> TcM (Maybe (CsExpr Tc, AnySigmaType))
tcInferAppHead_maybe fun = case fun of
  CsVar _ (L _ nm) -> Just <$> tcInferId nm
  ExprWithTySig _ e cs_ty -> Just <$> tcExprWithSig e cs_ty
  CsOverLit _ lit -> Just <$> tcInferOverLit lit
  _ -> return Nothing

addHeadCtxt :: AppCtxt -> TcM a -> TcM a 
addHeadCtxt fun_ctxt@(VACall{}) thing_inside
  | not (isGoodSrcSpan fun_loc)
  = thing_inside
  | otherwise
  = setSrcSpan fun_loc $ 
    case fun_ctxt of
      VACall{} -> thing_inside

  where
    fun_loc = appCtxtLoc fun_ctxt

{- *********************************************************************
*                                                                      *
                Expressions with a type signature
                        expr :: type
*                                                                      *
********************************************************************* -}

tcExprWithSig :: LCsExpr Rn -> LCsSigType (NoTc Rn) -> TcM (CsExpr Tc, AnySigmaType)
tcExprWithSig expr cs_ty = do
  sig_info <- checkNoErrs $ tcUserTypeSig loc cs_ty Nothing
  (expr', poly_ty) <- tcExprSig expr sig_info
  return (ExprWithTySig noExtField expr' cs_ty, poly_ty)
  where
    loc = getLocA cs_ty

tcExprSig :: LCsExpr Rn -> TcCompleteSig -> TcM (LCsExpr Tc, AnySigmaType)
tcExprSig expr sig = do
  expr' <- tcPolyLExprSig expr sig
  return (expr', varType (sig_bndr sig))

{- *********************************************************************
*                                                                      *
                 Overloaded literals
*                                                                      *
********************************************************************* -}

tcInferOverLit :: CsOverLit Rn -> TcM (CsExpr Tc, AnySigmaType)
tcInferOverLit lit@(OverLit { ol_val = val
                            , ol_ext = OverLitRn { ol_from_fun = L loc from_name } })
  = panic "tcInferOverLit"

{- *********************************************************************
*                                                                      *
                 tcInferId, tcCheckId
*                                                                      *
********************************************************************* -}

tcInferId :: Name -> TcM (CsExpr Tc, AnySigmaType)
tcInferId id_name
  | id_name `hasKey` assertIdKey
  = panic "tcInferId assert"
  | otherwise
  = do (expr, ty) <- tc_infer_id id_name
       traceTc "tcInferId" (ppr id_name <+> colon <+> ppr ty)
       return (expr, ty)

tc_infer_id :: Name -> TcM (CsExpr Tc, AnySigmaType)
tc_infer_id id_name = do
  thing <- tcLookup id_name
  case thing of
    ATcId { tct_id = id } -> do
      check_local_id id
      return_id id
    AGlobal (AnId id) -> return_id id
    AGlobal (AConLike (RealDataCon con)) -> tcInferDataCon con
    AGlobal (AConLike PatSynCon) -> panic "tc_infer_id impossible"
    (tcTyThingTyCon_maybe -> Just tc) -> panic "failIllegalTyCon WL_Anything (tyConName tc)"
    ATyVar name _ -> panic "failIllegalTyVal name"
    AKiVar name _ -> panic "failIllegalKiVal name"
    _ -> failWithTc $ panic "TcRnExpectedValueId thing"
  where
    return_id id = return (CsVar noExtField (noLocA id), varType id)

check_local_id :: AnyId -> TcM ()
check_local_id id = tcEmitBindingUsage $ singleUsageUE id

tcInferDataCon :: AnyDataCon -> TcM (CsExpr Tc, AnySigmaType)
tcInferDataCon con = return ( XExpr (ConLikeTc (RealDataCon con))
                            , dataConType con )

{- *********************************************************************
*                                                                      *
         Error reporting for function result mis-matches
*                                                                      *
********************************************************************* -}

addFunResCtxt :: CsExpr Tc -> [CsExprArg p] -> AnyType -> ExpRhoType -> TcM a -> TcM a
addFunResCtxt fun args fun_res_ty env_ty thing_inside = do
  env_tv <- asAnyTyKi <$> newOpenFlexiTyVarTy
  dumping <- doptM Opt_D_dump_tc_trace
  addLandmarkErrCtxtM (\env -> (env, ) <$> mk_msg dumping env_tv) thing_inside
  where
    mk_msg dumping env_tv = do
      mb_env_ty <- readExpType_maybe env_ty
      fun_res' <- zonkTcType fun_res_ty
      env' <- case mb_env_ty of
                Just env_ty -> zonkTcType env_ty
                Nothing -> do massert dumping
                              return env_tv
      let (_, _, fun_tau) = tcSplitNestedSigmaTys fun_res'
          (_, _, env_tau) = tcSplitNestedSigmaTys env'

          (args_fun, _, res_fun) = tcSplitFunTys fun_tau
          (args_env, _, res_env) = tcSplitFunTys env_tau
          n_fun = length args_fun
          n_env = length args_env
          info | n_fun > n_env
               , not_fun res_env
               = text "Probable cause:" <+> quotes (ppr fun)
                 <+> text "is applied to too few arguments"
               | n_fun < n_env
               , not_fun res_fun
               , (n_fun + count isValArg args) >= n_env
               = text "Possible cause:" <+> quotes (ppr fun)
                 <+> text "is applied to too many arguments"
               | otherwise
               = empty
      return info

    not_fun ty = case tcSplitTyConApp_maybe ty of
                   Just (tc, _) -> isAlgTyCon tc
                   Nothing -> False

{- *********************************************************************
*                                                                      *
             Misc utility functions
*                                                                      *
********************************************************************* -}

addExprCtxt :: CsExpr Rn -> TcRn a -> TcRn a
addExprCtxt e thing_inside = case e of
  CsUnboundVar {} -> thing_inside
  _ -> addErrCtxt (exprCtxt e) thing_inside

exprCtxt :: CsExpr Rn -> SDoc
exprCtxt expr = hang (text "In the expression:") 2 (ppr (stripParensCsExpr expr))
