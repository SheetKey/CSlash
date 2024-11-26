{-# LANGUAGE FlexibleContexts #-}

module CSlash.Rename.CsType where

import {-# SOURCE #-} CSlash.Rename.Bind (rnMatchGroup)

-- import GHC.Core.Type.FVs ( tyCoVarsOfTypeList )
-- import CSlash.Core.TyCon    ( isKindName )
import CSlash.Cs
import CSlash.Rename.Env
-- import GHC.Rename.Doc
import CSlash.Rename.Utils
  ( mapFvRn, bindLocalNamesFV
  , newLocalBndrRn, checkDupRdrNames
  , checkShadowedRdrNames, genCsTyApps, wrapGenSpan )
import CSlash.Rename.Fixity
   ( lookupFixityRn, lookupTyFixityRn )
import CSlash.Rename.Unbound ( notInScopeErr, WhereLooking(WL_LocalOnly) )
import CSlash.Rename.CsKind
import CSlash.Tc.Errors.Types
import CSlash.Tc.Errors.Ppr ( pprCsDocContext )
import CSlash.Tc.Utils.Monad
import CSlash.Unit.Module ( getModule )
import CSlash.Types.Name.Reader
import CSlash.Builtin.Names
import CSlash.Types.Name
import CSlash.Types.SrcLoc
import CSlash.Types.Name.Set
import CSlash.Types.Error
import CSlash.Types.Id.Make

import CSlash.Utils.Misc
import CSlash.Types.Fixity ( compareFixity, negateFixity
                           , Fixity(..), FixityDirection(..), LexicalFixity(..) )
import CSlash.Types.Basic  ( TypeOrKind(..) )
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Data.Maybe

import Data.List (nubBy, partition)
import Control.Monad

{- ******************************************************
*                                                       *
    CsSigType and CsPatSigType
*                                                       *
****************************************************** -}

rnCsSigType :: CsDocContext -> LCsSigType Ps -> RnM (LCsSigType Rn, FreeVars)
rnCsSigType doc (L l sig_ty@(CsSig _ body)) = do
  traceRn "rnCsSigType" (ppr sig_ty)
  rnLCsTypeWithKvs doc body $ \ (final_body, fvs) kv_nms ->
    return ( L l $ CsSig { sig_ext = kv_nms, sig_body = final_body }
           , fvs )

rnCsPatSigType
  :: CsDocContext
  -> CsPatSigType Ps
  -> (CsPatSigType Rn -> RnM (a, FreeVars))
  -> RnM (a, FreeVars)
rnCsPatSigType doc sig_ty thing_inside = do
  let pat_sig_ty = csPatSigType sig_ty

  rnLCsTypeWithKvs doc pat_sig_ty $ \ (final_pat_sig_ty, fvs1) kv_nms -> do
    let sig_names = CsPSRn kv_nms
        final_sig_ty = CsPS sig_names final_pat_sig_ty
    (res, fvs2) <- thing_inside final_sig_ty
    return (res, fvs1 `plusFV` fvs2)
                  
  -- rnImplicitKvOccs free_ki_vars $ \imp_kvs -> do
  --   let env = RTE ctx RnTypeBody
  --   (pat_sig_ty', fvs1) <- rnLCsTy env pat_sig_ty
  --   let sig_names = CsPSRn imp_kvs
  --       sig_ty' = CsPS sig_names pat_sig_ty'
  --   (res, fvs2) <- thing_inside sig_ty'
  --   return (res, fvs1 `plusFV` fvs2)                              

{- ******************************************************
*                                                       *
           LCsType and CsType
*                                                       *
****************************************************** -}

data RnTyEnv = RTE
  { rte_ctxt :: CsDocContext
  , rte_what :: RnTyWhat
  }

data RnTyWhat
  = RnTypeBody

instance Outputable RnTyEnv where
  ppr (RTE ctxt what)
    = text "RTE"  <+> braces (sep [ ppr what, pprCsDocContext ctxt ])

instance Outputable RnTyWhat where
  ppr RnTypeBody = text "RnTypeBody"

mkTyEnv :: CsDocContext -> RnTyWhat -> RnTyEnv
mkTyEnv ctxt what = RTE ctxt what

rnLCsType :: CsDocContext -> LCsType Ps -> RnM (LCsType Rn, FreeVars)
rnLCsType ctxt ty = rnLCsTy (mkTyEnv ctxt RnTypeBody) ty

rnLCsTy :: RnTyEnv -> LCsType Ps -> RnM (LCsType Rn, FreeVars)
rnLCsTy env (L loc ty) = setSrcSpanA loc $ do
  (ty', fvs) <- rnCsTy env ty
  return (L loc ty', fvs)

rnCsTy :: RnTyEnv -> CsType Ps -> RnM (CsType Rn, FreeVars)
rnCsTy env (CsForAllTy { cst_tele = tele, cst_body = tau }) = do
  bindCsForAllTelescope (rte_ctxt env) tele $ \ tele' -> do
    (tau', fvs) <- rnLCsTy env tau
    return
      ( CsForAllTy { cst_xforall = noExtField
                   , cst_tele = tele'
                   , cst_body = tau' }
      , fvs )

rnCsTy env (CsQualTy { cst_ctxt = lctxt, cst_body = tau }) = do
  (ctxt', fvs1) <- rnKiContext (rte_ctxt env) lctxt
  (tau', fvs2) <- rnLCsTy env tau
  return ( CsQualTy { cst_xqual = noExtField
                    , cst_ctxt = ctxt'
                    , cst_body = tau' }
         , fvs1 `plusFV` fvs2 )

rnCsTy env (CsTyVar _ ln@(L loc rdr_name)) = do
  massertPpr (isRdrTyLvl rdr_name) (text "rnCsTy CsTyVar" <+> ppr ln)
  name <- rnTyVar env rdr_name
  return (CsTyVar noAnn (L loc name), unitFV name)

rnCsTy env (CsUnboundTyVar _ v) = return (CsUnboundTyVar noExtField v, emptyFVs)

rnCsTy env (CsAppTy _ ty1 ty2) = do
  (ty1', fvs1) <- rnLCsTy env ty1
  (ty2', fvs2) <- rnLCsTy env ty2
  return (CsAppTy noExtField ty1' ty2', fvs1 `plusFV` fvs2)

rnCsTy env (CsFunTy _ arr ty1 ty2) = do
  (ty1', fvs1) <- rnLCsTy env ty1
  (ty2', fvs2) <- rnLCsTy env ty2
  (arr', fvs3) <- rnCsArrow env arr
  return ( CsFunTy noExtField arr' ty1' ty2'
         , plusFVs [fvs1, fvs2, fvs3] )

rnCsTy env (CsTupleTy x tys) = do
  (tys', fvs) <- mapFvRn rnTyTupArg tys
  return (CsTupleTy x tys', fvs)
  where
    rnTyTupArg (TyPresent x ty) = do
      (ty', fvs) <- rnLCsTy env ty
      return (TyPresent x ty', fvs)
    rnTyTupArg (TyMissing _) = return (TyMissing noExtField, emptyFVs)

rnCsTy env (CsSumTy x tys) = do
  (tys', fvs) <- mapFvRn (rnLCsTy env) tys
  return (CsSumTy x tys', fvs)

rnCsTy env (CsOpTy _ ty1 l_op ty2) = setSrcSpan (getLocA l_op) $ do
  let rdr_name = unLoc l_op
  massertPpr (isRdrTyLvl rdr_name) (text "rnCsTy CsOpTy" <+> ppr l_op)
  (l_op', fvs1) <- rnCsTyOp env l_op
  fix <- lookupTyFixityRn l_op'
  (ty1', fvs2) <- rnLCsTy env ty1
  (ty2', fvs3) <- rnLCsTy env ty2
  res_ty <- mkCsOpTyRn l_op' fix ty1' ty2'
  return (res_ty, plusFVs [fvs1, fvs2, fvs3])

rnCsTy env (CsParTy _ (L loc (section@(TySectionL {})))) = do
  (section', fvs) <- rnTySection env section
  return (CsParTy noAnn (L loc section'), fvs)

rnCsTy env (CsParTy _ (L loc (section@(TySectionR {})))) = do
  (section', fvs) <- rnTySection env section
  return (CsParTy noAnn (L loc section'), fvs)

rnCsTy env (CsParTy _ ty) = do
  (ty', fvs) <- rnLCsTy env ty
  return (CsParTy noAnn ty', fvs)

rnCsTy env section@(TySectionL {}) = do
  addErr (tySectionErr section)
  rnTySection env section

rnCsTy env section@(TySectionR {}) = do
  addErr (tySectionErr section)
  rnTySection env section

rnCsTy env (CsKindSig x ty k) = do
  (k', sig_fvs) <- rnLCsKind (rte_ctxt env) k
  (ty', lhs_fvs) <- rnLCsTy env ty
  return ( CsKindSig x ty' k'
         , lhs_fvs `plusFV` sig_fvs )

rnCsTy env (CsTyLamTy x matches) = do
  (matches', fvs_ms) <- rnMatchGroup TyLamTyAlt (rnLCsTy env) matches
  return (CsTyLamTy x matches', fvs_ms)

rnCsArrow :: RnTyEnv -> CsArrow Ps -> RnM (CsArrow Rn, FreeVars)
rnCsArrow env (CsArrow _ ki) = do
  (ki', fvs) <- rnLCsKind (rte_ctxt env) ki
  return (CsArrow noExtField ki', fvs)

rnTyVar :: RnTyEnv -> RdrName -> RnM Name
rnTyVar _ rdr_name = lookupTypeOccRn rdr_name

{- *****************************************************
*                                                      *
          Binding kind variables
*                                                      *
***************************************************** -}

rnLCsTypeWithKvs
  :: CsDocContext
  -> LCsType Ps
  -> ((LCsType Rn, FreeVars) -> [Name] -> RnM (a, FreeVars))
  -> RnM (a, FreeVars)
rnLCsTypeWithKvs doc lty thing_inside = do
  traceRn "rnLCsTypeWithKvs" (ppr lty)
  let kv_occs = extractCsTyRdrKindVars lty
      bndrs_loc = case map getLocA kv_occs of
        [] -> panic "bindCsKiVars/bndrs_loc"
        [loc] -> loc
        loc:locs -> loc `combineSrcSpans` last locs
  traceRn "kv_occs" (ppr kv_occs)

  rnImplicitKvOccs kv_occs $ \kv_nms -> do
    let kv_nms_final = map (`setNameLoc` bndrs_loc) kv_nms
    traceRn "kv_nms" (ppr kv_nms_final)

    stuff <- rnLCsType doc lty

    thing_inside stuff kv_nms

-- bindHsQTyVars
-- We require all type variables to be bound (by forall or lambda)
-- All kind variables are implicitly universally quantified (no user quantification)
-- bindCsKiVars -- NOTE: this should be renamed since nothing is bound
--   :: CsDocContext
--   -> FreeKiVars
--   -> ([Name] -> RnM (b, FreeVars))
--   -> RnM (b, FreeVars)
-- bindCsKiVars doc all_kv_occs thing_inside = do
--   traceRn "checkMixedVars3" $
--     vcat [ text "all_kv_occs" <+> ppr all_kv_occs ]

--   rnImplicitKvOccs all_kv_occs $ \ all_kv_nms' -> do
--     let all_kv_nms = map (`setNameLoc` bndrs_loc) all_kv_nms'
--     traceRn "bindCsKiVars" (ppr all_kv_nms)
--     thing_inside all_kv_nms
--   where
--     bndrs_loc = case map getLocA all_kv_occs of
--       [] -> panic "bindCsKiVars/bndrs_loc"
--       [loc] -> loc
--       loc:locs -> loc `combineSrcSpans` last locs

data WarnUnusedForalls
  = WarnUnusedForalls
  | NoWarnUnusedForalls

instance Outputable WarnUnusedForalls where
  ppr wuf = text $ case wuf of
    WarnUnusedForalls   -> "WarnUnusedForalls"
    NoWarnUnusedForalls -> "NoWarnUnusedForalls"

bindCsForAllTelescope
  :: CsDocContext
  -> CsForAllTelescope Ps
  -> (CsForAllTelescope Rn -> RnM (a, FreeVars))
  -> RnM (a, FreeVars)
bindCsForAllTelescope doc (CsForAll _ bndrs) thing_inside = 
  bindLCsTyVarBndrs doc WarnUnusedForalls bndrs $ \bndrs' ->
    thing_inside $ mkCsForAllTele noAnn bndrs'

bindLCsTyVarBndrs
  :: CsDocContext
  -> WarnUnusedForalls
  -> [LCsTyVarBndr Ps]
  -> ([LCsTyVarBndr Rn] -> RnM (b, FreeVars))
  -> RnM (b, FreeVars)
bindLCsTyVarBndrs doc wuf tv_bndrs thing_inside = do
  checkShadowedRdrNames tv_names_w_loc
  checkDupRdrNames tv_names_w_loc
  go tv_bndrs thing_inside
  where
    tv_names_w_loc = map csLTyVarLocName tv_bndrs

    go [] thing_inside = thing_inside []
    go (b:bs) thing_inside = bindLCsTyVarBndr doc b $ \b' -> do
      (res, fvs) <- go bs $ \bs' -> thing_inside (b' : bs')
      warn_unused b' fvs
      return (res, fvs)

    warn_unused tv_bndr fvs = case wuf of
      WarnUnusedForalls -> warnUnusedForAll doc tv_bndr fvs
      NoWarnUnusedForalls -> return ()

bindLCsTyVarBndr
  :: CsDocContext
  -> LCsTyVarBndr Ps
  -> (LCsTyVarBndr Rn -> RnM (b, FreeVars))
  -> RnM (b, FreeVars)
bindLCsTyVarBndr doc (L loc (KindedTyVar x lrdr@(L lv _) kind)) thing_inside = do
  (kind', fvs1) <- rnLCsKind doc kind
  tv_nm <- newTyVarNameRn lrdr
  (b, fvs2) <- bindLocalNamesFV [tv_nm] $ thing_inside (L loc (KindedTyVar x (L lv tv_nm) kind'))
  return (b, fvs1 `plusFV` fvs2)
bindLCsTyVarBndr doc (L loc (ImpKindedTyVar x lrdr@(L lv _) kind)) thing_inside = do
  (kind', fvs1) <- rnLCsKind doc kind
  tv_nm <- newTyVarNameRn lrdr
  (b, fvs2) <- bindLocalNamesFV [tv_nm]
               $ thing_inside (L loc (ImpKindedTyVar x (L lv tv_nm) kind'))
  return (b, fvs1 `plusFV` fvs2)

newTyVarNameRn :: LocatedN RdrName -> RnM Name
newTyVarNameRn = new_tv_name_rn newLocalBndrRn

new_tv_name_rn :: (LocatedN RdrName -> RnM Name) -> LocatedN RdrName -> RnM Name
new_tv_name_rn cont lrdr = cont lrdr

{- *********************************************************************
*                                                                      *
            Fixities and precedence parsing
*                                                                      *
********************************************************************* -}

rnCsTyOp :: RnTyEnv -> LocatedN RdrName -> RnM (LocatedN Name, FreeVars)
rnCsTyOp env (L loc op) = do
  op' <- rnTyVar env op
  return (L loc op', unitFV op')

mkCsOpTyRn :: LocatedN Name -> Fixity -> LCsType Rn -> LCsType Rn -> RnM (CsType Rn)
mkCsOpTyRn op1 fix1 ty1 (L loc2 (CsOpTy _ ty2a op2 ty2b)) = do
  fix2 <- lookupTyFixityRn op2
  mk_cs_op_ty op1 fix1 ty1 op2 fix2 ty2a ty2b loc2
mkCsOpTyRn op1 _ ty1 ty2 = return (CsOpTy noAnn ty1 op1 ty2)

mk_cs_op_ty
  :: LocatedN Name -> Fixity -> LCsType Rn
  -> LocatedN Name -> Fixity -> LCsType Rn
  -> LCsType Rn -> SrcSpanAnnA -> RnM (CsType Rn)
mk_cs_op_ty op1 fix1 ty1 op2 fix2 ty2a ty2b loc2
  | nofix_error
  = do precParseErr (NormalOp (unLoc op1), fix1) (NormalOp (unLoc op2), fix2)
       return (ty1 `op1ty` (L loc2 (ty2a `op2ty` ty2b)))
  | associate_right
  = return (ty1 `op1ty` (L loc2 (ty2a `op2ty` ty2b)))
  | otherwise
  = do new_ty <- mkCsOpTyRn op1 fix1 ty1 ty2a
       return (noLocA new_ty `op2ty` ty2b)
  where
    lhs `op1ty` rhs = CsOpTy noAnn lhs op1 rhs
    lhs `op2ty` rhs = CsOpTy noAnn lhs op2 rhs
    (nofix_error, associate_right) = compareFixity fix1 fix2

rnTySection :: RnTyEnv -> CsType Ps -> RnM (CsType Rn, FreeVars)
rnTySection env section@(TySectionR x op ty) = do
  (op', fvs_op) <- rnLCsTy env op
  (ty', fvs_ty) <- rnLCsTy env ty
  checkTySectionPrec InfixR section op' ty'
  let -- rn_section = TySectionR x op' ty'
      ds_section = genCsTyApps rightTySectionName [op', ty']
  return (ds_section, fvs_op `plusFV` fvs_ty)
rnTySection env section@(TySectionL x ty op) = do
  (ty', fvs_ty) <- rnLCsTy env ty
  (op', fvs_op) <- rnLCsTy env op
  checkTySectionPrec InfixL section op' ty'
  let -- rn_section = SectionL x ty' op'
      ds_section = genCsTyApps leftTySectionName [wrapGenSpan $ CsAppTy noExtField op' ty']
  return (ds_section, fvs_op `plusFV` fvs_ty)
rnTySection _ ty = pprPanic "rnTySection" (ppr ty)

tySectionErr :: CsType Ps -> TcRnMessage
tySectionErr _ = panic "TcRnTySectionWithoutParentheses"

get_tyop :: LCsType Rn -> OpName
get_tyop (L _ (CsTyVar _ n)) = NormalOp (unLoc n)
get_tyop (L _ (CsUnboundTyVar _ uv)) = UnboundOp uv
get_tyop other = pprPanic "get_tyop" (ppr other)

checkTySectionPrec :: FixityDirection -> CsType Ps -> LCsType Rn -> LCsType Rn -> RnM ()
checkTySectionPrec direction section op arg = case unLoc arg of
  CsOpTy _ _ (L _ op') _ -> do
    op_fix@(Fixity op_prec _) <- lookupTyFixityOp (get_tyop op)
    arg_fix@(Fixity arg_prec assoc) <- lookupFixityRn op'
    unless (op_prec < arg_prec
            || (op_prec == arg_prec && direction == assoc))
      $ tySectionPrecErr
        (get_tyop op, op_fix)
        (NormalOp op', arg_fix)
        section
  _ -> return ()

lookupTyFixityOp :: OpName -> RnM Fixity
lookupTyFixityOp (NormalOp n) = lookupFixityRn n
lookupTyFixityOp (UnboundOp u) = lookupFixityRn (mkUnboundName (occName u))
lookupTyFixityOp NegateOp = panic "lookupTyFixityOp NegateOp"

tySectionPrecErr :: (OpName, Fixity) -> (OpName, Fixity) -> CsType Ps -> RnM ()
tySectionPrecErr op@(n1, _) arg_op@(n2, _) section
  | is_unbound n1 || is_unbound n2
  = return ()
  | otherwise
  = panic "addErr $ TcRnTySectionPrecedenceError op arg_op section"

mkOpAppRn :: LCsExpr Rn -> LCsExpr Rn -> Fixity -> LCsExpr Rn -> RnM (CsExpr Rn)
-- (e1a `op1` e1b) `op2` e2
mkOpAppRn e1@(L _ (OpApp fix1 e1a op1 e1b)) op2 fix2 e2
  | nofix_error
  = do precParseErr (get_op op1, fix1) (get_op op2, fix2)
       return (OpApp fix2 e1 op2 e2)
  | associate_right
  = do new_e <- mkOpAppRn e1b op2 fix2 e2
       return (OpApp fix1 e1a op1 (L loc' new_e))
  where
    loc' = combineLocsA e1b e2
    (nofix_error, associate_right) = compareFixity fix1 fix2

mkOpAppRn e1 op fix e2
  = assertPpr (right_op_ok fix (unLoc e2))
    (ppr e1 $$ text "---" $$ ppr op $$ text "---" $$ ppr fix $$ text "---" $$ ppr e2)
    $ return (OpApp fix e1 op e2)

get_op :: LCsExpr Rn -> OpName
get_op (L _ (CsVar _ n)) = NormalOp (unLoc n)
get_op (L _ (CsUnboundVar _ uv)) = UnboundOp uv
get_op other = pprPanic "get_op" (ppr other)

right_op_ok :: Fixity -> CsExpr Rn -> Bool
right_op_ok fix1 (OpApp fix2 _ _ _)
  = not error_please && associate_right
  where (error_please, associate_right) = compareFixity fix1 fix2
right_op_ok _ _ = True

mkNegAppRn :: LCsExpr Rn -> SyntaxExpr Rn -> RnM (CsExpr Rn)
mkNegAppRn neg_arg neg_name
  = assert (not_op_app (unLoc neg_arg))
    $ return (NegApp noExtField neg_arg neg_name)

not_op_app :: CsExpr id -> Bool
not_op_app (OpApp {}) = False
not_op_app _ = True

checkSectionPrec :: FixityDirection -> CsExpr Ps -> LCsExpr Rn -> LCsExpr Rn -> RnM ()
checkSectionPrec direction section op arg = case unLoc arg of
  OpApp fix _ op' _ -> go_for_it (get_op op') fix
  NegApp _ _ _ -> go_for_it NegateOp negateFixity
  _ -> return ()
  where
    op_name = get_op op
    go_for_it arg_op arg_fix@(Fixity arg_prec assoc) = do
      op_fix@(Fixity op_prec _) <- lookupFixityOp op_name
      unless (op_prec < arg_prec
              || (op_prec == arg_prec && direction == assoc))
        (sectionPrecErr (get_op op, op_fix) (arg_op, arg_fix) section)

lookupFixityOp :: OpName -> RnM Fixity
lookupFixityOp (NormalOp n) = lookupFixityRn n
lookupFixityOp NegateOp = lookupFixityRn negateName
lookupFixityOp (UnboundOp u) = lookupFixityRn (mkUnboundName (occName u))

precParseErr :: (OpName, Fixity) -> (OpName, Fixity) -> RnM ()
precParseErr op1@(n1, _) op2@(n2, _)
  | is_unbound n1 || is_unbound n2
  = return ()
  | otherwise
  = panic "addErr $ TcRnPrecedenceParsingError op1 op2"

sectionPrecErr :: (OpName, Fixity) -> (OpName, Fixity) -> CsExpr Ps -> RnM ()
sectionPrecErr op@(n1, _) arg_op@(n2, _) section
  | is_unbound n1 || is_unbound n2
  = return ()
  | otherwise
  = panic "addErr $ TcRnSectionPrecedenceError op arg_op section"

is_unbound :: OpName -> Bool
is_unbound (NormalOp n) = isUnboundName n
is_unbound UnboundOp{} = True
is_unbound _ = False

{- *****************************************************
*                                                      *
                 Errors
*                                                      *
***************************************************** -}

warnUnusedForAll :: CsDocContext -> LCsTyVarBndr Rn -> FreeVars -> TcM ()
warnUnusedForAll doc (L loc tv) used_names
  = unless (csTyVarName tv `elemNameSet` used_names) $ 
    let msg = panic "TcRnUnusedQuantifiedTypeVar doc tv"
    in addDiagnosticAt (locA loc) msg

{- *********************************************************************
*                                                                      *
      Finding the free kind variables of a (CsType RdrName)
*                                                                      *
********************************************************************* -}

{-
We have two major differences compared to GHC:
  1. All type variables must be bound. E.g., by forall or a type lambda.
  2. Kind variables cannot be explicitly quantified, but are always implicitly universally
     quantified. 
-}

-- Extract ALL the free kind variables from a CsType.
-- In GHC, order of the result list matters for scoping:
-- The kvs in the result type signature should be last in the list since
-- GHC checks that these are quantified earlier.
-- We don't care; all kvs are implicitly quantified; we don't allow explicit quantification.
-- We list them in the order they appear from left to right. 
extractCsTyRdrKindVars :: LCsType Ps -> FreeKiVars
extractCsTyRdrKindVars (L _ ty) = case ty of
  CsForAllTy _ tele ty -> extractCsForAllTelescopeKindVars tele ++ extractCsTyRdrKindVars ty
  CsQualTy _ c ty -> extractCsContextKindVars c ++ extractCsTyRdrKindVars ty
  CsAppTy _ ty1 ty2 -> extractCsTyRdrKindVars ty1 ++ extractCsTyRdrKindVars ty2
  CsFunTy _ arr ty1 ty2 -> extractCsTyRdrKindVars ty1
                           ++ extractCsArrowKindVars arr
                           ++ extractCsTyRdrKindVars ty2
  CsTupleTy _ tys -> concatMap extractCsTyTupArgKindVars tys
  CsSumTy _ tys -> concatMap extractCsTyRdrKindVars tys
  CsOpTy _ ty1 _ ty2 -> extractCsTyRdrKindVars ty1 ++ extractCsTyRdrKindVars ty2
  CsParTy _ ty -> extractCsTyRdrKindVars ty
  CsKindSig _ ty ki -> extractCsTyRdrKindVars ty ++ extractCsKindKindVars ki
  CsTyLamTy _ mg -> extractCsTyMGKindVars mg
  TySectionL _ ty1 ty2 -> extractCsTyRdrKindVars ty1 ++ extractCsTyRdrKindVars ty2
  TySectionR _ ty1 ty2 -> extractCsTyRdrKindVars ty1 ++ extractCsTyRdrKindVars ty2
  _ -> []

extractCsForAllTelescopeKindVars :: CsForAllTelescope Ps -> FreeKiVars
extractCsForAllTelescopeKindVars (CsForAll { csf_bndrs = bndrs })
  = concatMap extractCsTyVarBndrsKindVars bndrs

extractCsTyVarBndrsKindVars :: LCsTyVarBndr Ps -> FreeKiVars
extractCsTyVarBndrsKindVars (L _ (KindedTyVar _ _ ki)) = extractCsKindKindVars ki
extractCsTyVarBndrsKindVars (L _ (ImpKindedTyVar _ _ ki)) = extractCsKindKindVars ki

extractCsContextKindVars :: LCsContext Ps -> FreeKiVars
extractCsContextKindVars (L _ ctxt)
  = concatMap extractCsKdRelKindVars ctxt

extractCsKdRelKindVars :: LCsKdRel Ps -> FreeKiVars
extractCsKdRelKindVars (L _ rel) = case rel of
  CsKdLT _ k1 k2 -> extractCsKindKindVars k1 ++ extractCsKindKindVars k2
  CsKdLTEQ _ k1 k2 -> extractCsKindKindVars k1 ++ extractCsKindKindVars k2

extractCsArrowKindVars :: CsArrow Ps -> FreeKiVars
extractCsArrowKindVars (CsArrow _ ki) = extractCsKindKindVars ki

extractCsTyTupArgKindVars :: CsTyTupArg Ps -> FreeKiVars
extractCsTyTupArgKindVars (TyPresent _ ty) = extractCsTyRdrKindVars ty
extractCsTyTupArgKindVars _ = []

extractCsTyMGKindVars :: MatchGroup Ps (LCsType Ps) -> FreeKiVars
extractCsTyMGKindVars (MG _ (L _ alts)) = concatMap extractCsTyMatchKindVars alts

extractCsTyMatchKindVars :: LMatch Ps (LCsType Ps) -> FreeKiVars
extractCsTyMatchKindVars (L _ (Match _ _ (L _ pats) grhss))
  = concatMap extractCsTyPatKindVars pats ++ extractCsTyGRHSsKindVars grhss

extractCsTyPatKindVars :: LPat Ps -> FreeKiVars
extractCsTyPatKindVars (L _ pat) = case pat of
  ParPat _ lpat -> extractCsTyPatKindVars lpat
  KdSigPat _ lpat ksig -> extractCsTyPatKindVars lpat ++ extractCsPatSigKindKindVars ksig
  ImpPat _ lpat -> extractCsTyPatKindVars lpat
  _ -> []
  
extractCsPatSigKindKindVars :: CsPatSigKind (NoTc Ps) -> FreeKiVars
extractCsPatSigKindKindVars (CsPSK _ ki) = extractCsKindKindVars ki

extractCsTyGRHSsKindVars :: GRHSs Ps (LCsType Ps) -> FreeKiVars
extractCsTyGRHSsKindVars (GRHSs _ grhss)
  = concatMap extractCsTyGRHSKindVars grhss

extractCsTyGRHSKindVars :: LGRHS Ps (LCsType Ps) -> FreeKiVars
extractCsTyGRHSKindVars (L _ (GRHS _ [] ty)) = extractCsTyRdrKindVars ty
extractCsTyGRHSKindVars (L _ (GRHS _ stmt _)) = pprPanic "extractCsTyGRHSKindVars" (ppr stmt)

extractCsKindKindVars :: LCsKind Ps -> FreeKiVars
extractCsKindKindVars ki = extract_lki ki []

extract_lki :: LCsKind Ps -> FreeKiVars -> FreeKiVars
extract_lki (L _ ki) acc = case ki of
  CsUKd {} -> acc
  CsAKd {} -> acc
  CsLKd {} -> acc
  CsKdVar _ lkv -> extract_kv lkv acc
  CsFunKd _ ki1 ki2 -> extract_lki ki1 $ extract_lki ki2 acc
  CsParKd _ ki -> extract_lki ki acc

extract_kv :: LocatedN RdrName -> FreeKiVars -> FreeKiVars
extract_kv kv acc =
  assertPpr (isRdrKiVar (unLoc kv) && (not . isQual) (unLoc kv)) (text "extact_kv:" <+> ppr kv)
  $ kv : acc
