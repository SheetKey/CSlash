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
-- import GHC.Tc.Utils.Instantiate ( tcInstInvisibleTyBinders, tcInstInvisibleTyBindersN,
--                                   tcInstInvisibleTyBinder, tcSkolemiseInvisibleBndrs,
--                                   tcInstTypeBndrs )
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

{- *********************************************************************
*                                                                      *
             The main kind checker (no validity checks)
*                                                                      *
********************************************************************* -}

tcCheckLCsType :: LCsType Rn -> ContextKind -> TcM TcType
tcCheckLCsType cs_ty exp_kind = addTypeCtxt cs_ty $ do
  ek <- newExpectedKind exp_kind
  tcLCsType cs_ty ek

------------------------------------------
tc_infer_lcs_type :: LCsType Rn -> TcM (TcType, TcKind)
tc_infer_lcs_type (L span ty) = setSrcSpanA span $ tc_infer_cs_type ty

---------------------------
tc_infer_cs_type_ek :: HasDebugCallStack => CsType Rn -> TcKind -> TcM TcType
tc_infer_cs_type_ek cs_ty ek = do
  (ty, k) <- tc_infer_cs_type cs_ty
  checkExpectedKind cs_ty ty k ek

---------------------------
tc_infer_cs_type :: CsType Rn -> TcM (TcType, TcKind)

tc_infer_cs_type (CsParTy _ ty) = tc_infer_lcs_type ty

tc_infer_cs_type ty
  | Just (cs_fun_ty, cs_args) <- splitCsAppTys ty
  = do (fun_ty, _) <- tcInferTyAppHead cs_fun_ty
       tcInferTyApps cs_fun_ty fun_ty cs_args

tc_infer_cs_type (CsKindSig _ ty sig) = do
  sig' <- tcLCsKindSig KindSigCtxt sig
  traceTc "tc_infer_cs_type:sig" (ppr ty $$ ppr sig')
  ty' <- tc_lcs_type ty sig'
  return (ty', sig')

tc_infer_cs_type other_ty = do
  kv <- newMetaKindVar
  ty' <- tc_cs_type other_ty kv
  return (ty', kv)

------------------------------------------
tcLCsType :: LCsType Rn -> TcKind -> TcM TcType
tcLCsType = tc_lcs_type

tc_lcs_type :: LCsType Rn -> TcKind -> TcM TcType
tc_lcs_type (L span ty) exp_kind = setSrcSpanA span $
  tc_cs_type ty exp_kind

tc_cs_type :: CsType Rn -> TcKind -> TcM TcType

tc_cs_type (CsParTy _ ty) exp_kind = tc_lcs_type ty exp_kind

tc_cs_type (CsFunTy _ arr_kind ty1 ty2) exp_kind
  = tc_fun_type arr_kind ty1 ty2 exp_kind

tc_cs_type t@(CsForAllTy { cst_tele = tele, cst_body = ty }) exp_kind
  = tc_cs_forall_ty tele ty exp_kind
  where
    tc_cs_forall_ty tele ty ek = do
      (tv_bndrs, ty') <- tcTkTelescope tele $ tc_lcs_type ty exp_kind
      return $ mkForAllTys tv_bndrs ty'

tc_cs_type (CsQualTy { cst_ctxt = ctxt, cst_body = rn_ty }) exp_kind = panic "tc_cs_type QualTy"

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
  tau_tys <- zipWithM tc_lcs_type cs_tys arg_kinds
  let sum_ty = mkTyConApp (sumTyCon arity) tau_tys
      sum_kind = panic "sum_kind"
  checkExpectedKind rn_ty sum_ty sum_kind exp_kind

tc_cs_type ty@(CsTyVar {}) ek = tc_infer_cs_type_ek ty ek
tc_cs_type ty@(CsAppTy {}) ek = tc_infer_cs_type_ek ty ek
tc_cs_type ty@(CsOpTy {}) ek = tc_infer_cs_type_ek ty ek
tc_cs_type ty@(CsKindSig {}) ek = tc_infer_cs_type_ek ty ek

tc_cs_type _ _ = panic "tc_cs_type unfinished"

------------------------------------------
tc_fun_type :: CsArrow Rn -> LCsType Rn -> LCsType Rn -> TcKind -> TcM TcType
tc_fun_type arr_kind ty1 ty2 exp_kind = do
  traceTc "tc_fun_type" (ppr ty1 $$ ppr ty2)
  arg_k <- newOpenTypeKind
  res_k <- newOpenTypeKind
  ty1' <- tc_lcs_type ty1 arg_k
  ty2' <- tc_lcs_type ty2 res_k
  arr_kind' <- tc_arrow arr_kind
  checkExpectedKind (CsFunTy noExtField arr_kind ty1 ty2)
                    (tcMkFunTy arr_kind' ty1' ty2')
                    arr_kind' exp_kind

tc_arrow :: CsArrow Rn -> TcM TcKind
tc_arrow _ = panic "tc_arrow"

{- *********************************************************************
*                                                                      *
                Tuples
*                                                                      *
********************************************************************* -}

tc_tuple :: CsType Rn -> TcKind -> TcM TcType
tc_tuple rn_ty@(CsTupleTy _ tup_args) exp_kind = do
  let arity = length tys
      tys = (\case { TyPresent _ ty -> ty; _ -> panic "tc_tuple" }) <$> tup_args
  arg_kinds <- replicateM arity newOpenTypeKind
  tau_tys <- zipWithM tc_lcs_type tys arg_kinds
  finish_tuple rn_ty tau_tys arg_kinds exp_kind
tc_tuple _ _ = panic "tc_tuple/unreachable"

finish_tuple :: CsType Rn -> [TcType] -> [TcKind] -> TcKind -> TcM TcType
finish_tuple rn_ty tau_tys tau_kinds exp_kind = do
  traceTc "finish_tuple" (ppr tau_kinds $$ ppr exp_kind)
  let arity = length tau_tys
      tycon = tupleTyCon arity
      res_kind = panic "tuple_kind"
  checkTupSize arity
  checkExpectedKind rn_ty (mkTyConApp tycon tau_tys) res_kind exp_kind

---------------------------
tcInferTyApps :: LCsType Rn -> TcType -> [LCsTypeArg Rn] -> TcM (TcType, TcKind)
tcInferTyApps cs_ty fun cs_args = do
  (f_args, res_k) <- tcInferTyApps_nosat cs_ty fun cs_args
  saturateFamApp f_args res_k

tcInferTyApps_nosat :: LCsType Rn -> TcType -> [LCsTypeArg Rn] -> TcM (TcType, TcKind)
tcInferTyApps_nosat orig_cs_ty fun orig_cs_args = do
  traceTc "tcInferTyApps {" (ppr orig_cs_ty $$ ppr orig_cs_args)
  (f_args, res_k) <- go_init 1 fun orig_cs_args
  traceTc "tcInferTyApps }" (ppr f_args <+> colon <+> ppr res_k)
  return (f_args, res_k)
  where
    go_init n fun all_args = go n fun empty_subst fun_ki all_args
      where
        fun_ki = typeKind fun
        empty_subst = mkEmptySubst $ mkInScopeSet $ kiVarsOfKind fun_ki

    go :: Int -> TcType -> Subst -> TcKind -> [LCsTypeArg Rn] -> TcM (TcType, TcKind)
    go n fun subst fun_ki all_args = case (all_args, tcSplitFunKi_maybe fun_ki) of
      ([], _) -> return (fun, substKd subst fun_ki)
      (CsArgPar _ : args, _) -> go n fun subst fun_ki args
      (CsValArg _ arg : args, Just (arg_ki, res_ki)) -> do
        traceTc "tcInferTyApps (vis normal app)"
          $ vcat [ ppr arg_ki, ppr arg, ppr subst ]
        arg' <- addErrCtxt (funAppCtxt orig_cs_ty arg n)
                $ tc_lcs_type arg arg_ki
        traceTc "tcInferTyApps (vis normal app) 2" (ppr arg_ki)
        (subst', fun') <- mkAppTyM subst fun arg_ki arg'
        go (n + 1) fun' subst' res_ki args

      (CsValArg _ _ : _, Nothing) -> try_again_after_substing_or $ do
        panic "body"
      
      (CsTypeArg {} : _, _) -> panic "tcInferTyApps/go/CsTypeArg"

      where
        try_again_after_substing_or fallthrough
          | not (isEmptyKvSubst subst)
          = go n fun zapped_subst substed_fun_ki all_args
          | otherwise
          = fallthrough

        zapped_subst = zapSubst subst
        substed_fun_ki = substKd subst fun_ki

mkAppTyM :: Subst -> TcType -> TcKind -> TcType -> TcM (Subst, TcType)
mkAppTyM subst fun fun_ki arg = panic "mkAppTyM"

saturateFamApp :: TcType -> TcKind -> TcM (TcType, TcKind)
saturateFamApp ty kind = panic "saturateFamApp"

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
tcInferTyAppHead :: LCsType Rn -> TcM (TcType, TcKind)
tcInferTyAppHead (L _ (CsTyVar _ (L _ tv))) = tcTyVar tv
tcInferTyAppHead (L _ (CsUnboundTyVar _ _)) = panic "tcInferTyAppHead/unbound ty var"
tcInferTyAppHead ty = tc_infer_lcs_type ty

{- *********************************************************************
*                                                                      *
                checkExpectedKind
*                                                                      *
********************************************************************* -}

checkExpectedKind :: HasDebugCallStack => CsType Rn -> TcType -> TcKind -> TcKind -> TcM TcType
checkExpectedKind cs_ty ty act_kind exp_kind = do
  traceTc "checkExpectedKind" (ppr ty $$ ppr act_kind)

  let origin = KindEqOrigin { keq_actual = act_kind
                            , keq_expected = exp_kind
                            , keq_thing = Just $ CsTypeRnThing cs_ty }

  traceTc "checkExpectedKindX"
    $ vcat [ ppr cs_ty
           , text "act_kind:" <+> ppr act_kind
           , text "exp_kind:" <+> ppr exp_kind ]

  if act_kind `tcEqKind` exp_kind
    then return ty
    else do unifyKindAndEmit origin act_kind exp_kind
            return ty

tcTyVar :: Name -> TcM (TcType, TcKind)
tcTyVar name = do
  traceTc "lk1" (ppr name)
  thing <- tcLookup name
  case thing of
    ATyVar _ tv -> return (mkTyVarTy tv, tyVarKind tv)
    (tcTyThingTyCon_maybe -> Just tc) -> return (mkTyConTy tc, tyConKind tc)
    _ -> panic "wrongThingErr WrongThingType thing name"

addTypeCtxt :: LCsType Rn -> TcM a -> TcM a
addTypeCtxt (L _ ty) thing = addErrCtxt doc thing
  where
    doc = text "In the type" <+> quotes (ppr ty)

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
  -> TyConFlavor TyCon
  -> [Name]
  -> TcM (Kind, Kind, Arity)
  -> TcM TcTyCon
kcDeclHeader InitialKindInfer = kcInferDeclHeader

-- Note: arity is not the number of args the TyCon can accept,
-- it is the number of args the TyCon accepts before its kind is the result kind
kcInferDeclHeader
  :: Name
  -> TyConFlavor TyCon
  -> [Name]
  -> TcM (Kind, Kind, Arity) -- (resultkind, fullkind, arity)
  -> TcM MonoTcTyCon
kcInferDeclHeader name flav kv_ns kc_res_ki = addTyConFlavCtxt name flav $ do
  (scoped_kvs, (res_kind, full_kind, arity)) <- bindImplicitKinds kv_ns kc_res_ki

  let kv_pairs = mkKiVarNamePairs scoped_kvs
      tycon = mkTcTyCon name res_kind full_kind arity kv_pairs False flav
  
  traceTc "kcInferDeclHeader"
    $ vcat [ ppr name, ppr kv_ns, ppr scoped_kvs, ppr res_kind, ppr full_kind, ppr arity ]

  return tycon

{- *********************************************************************
*                                                                      *
             Expected kinds
*                                                                      *
********************************************************************* -}

data ContextKind
  = TheKind TcKind
  | AnyKind

newExpectedKind :: ContextKind -> TcM TcKind
newExpectedKind (TheKind k) = return k
newExpectedKind AnyKind = newMetaKindVar

{- *********************************************************************
*                                                                      *
             Bringing type variables into scope
*                                                                      *
********************************************************************* -}

--------------------------------------
--    HsForAllTelescope
--------------------------------------

tcTkTelescope :: CsForAllTelescope Rn -> TcM a -> TcM ([TcTyVarBinder], a)
tcTkTelescope (CsForAll { csf_bndrs = bndrs }) thing_inside = do
  -- skol_info <- mkSkolemInfo $ ForAllSkol $ CsTyVarBndrsRn $ unLoc <$> bndrs
  -- let skol_mode = smVanilla 
  panic "tcTkTelescope"

newKiVarBndr :: Name -> TcM TcKiVar
newKiVarBndr name = do
  details <- newMetaDetailsK KiVarKind
  return $ mkTcKiVar name details
  
--------------------------------------
--    Implicit kind var binders
--------------------------------------

bindImplicitKinds :: [Name] -> TcM a -> TcM ([TcKiVar], a)
bindImplicitKinds kv_names thing_inside = do
  lcl_env <- getLclTypeEnv
  kvs <- mapM (new_kv lcl_env) kv_names
  traceTc "bindImplicitKinds" (ppr kv_names $$ ppr kvs)
  res <- tcExtendNameKiVarEnv (kv_names `zip` kvs) thing_inside
  return (kvs, res)
  where
    new_kv lcl_env name
      | Just (AKiVar _ kv) <- lookupNameEnv lcl_env name
      = return kv
      | otherwise
      = newKiVarBndr name

{- *********************************************************************
*                                                                      *
             Kind generalization
*                                                                      *
********************************************************************* -}

kindGeneralizeNone :: TcKind -> TcM ()
kindGeneralizeNone kind = do
  traceTc "kindGeneralizeNone" (ppr kind)
  dvs <- candidateQKiVarsOfKind kind
  _ <- promoteKiVarSet $ dVarSetToVarSet dvs
  return ()

{- *********************************************************************
*                                                                      *
                Sort checking kinds
*                                                                      *
********************************************************************* -}

tcLCsKindSig :: UserTypeCtxt -> LCsKind Rn -> TcM Kind
tcLCsKindSig ctxt cs_kind = do
  kind <- addErrCtxt (text "In the kind" <+> quotes (ppr cs_kind))
          $ tcLCsKind cs_kind
  traceTc "tcLCsKindSig" (ppr cs_kind $$ ppr kind)

  kindGeneralizeNone kind
  kind <- liftZonkM $ zonkTcKind kind

  checkValidKind ctxt kind
  traceTc "tcLCsKindSig2" (ppr kind)
  return kind

tcLCsContext :: LCsContext Rn -> TcM [KdRel]
tcLCsContext context = panic "tcLCsContext"

{- *********************************************************************
*                                                                      *
             Error messages
*                                                                      *
********************************************************************* -}

funAppCtxt :: (Outputable fun, Outputable arg) => fun -> arg -> Int -> SDoc
funAppCtxt fun arg arg_no = hang (hsep [ text "In the", speakNth arg_no, text "argument of"
                                       , quotes (ppr fun) <> text ", namely" ])
                            2 (quotes (ppr arg))

addTyConFlavCtxt :: Name -> TyConFlavor tc -> TcM a -> TcM a
addTyConFlavCtxt name flav
  = addErrCtxt $ hsep [ text "In the", ppr flav
                      , text "declaration for"
                      , quotes (ppr name) ]
