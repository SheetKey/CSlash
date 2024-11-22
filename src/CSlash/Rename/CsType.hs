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

rnCsPatSigType
  :: CsDocContext
  -> CsPatSigType Ps
  -> (CsPatSigType Rn -> RnM (a, FreeVars))
  -> RnM (a, FreeVars)
rnCsPatSigType ctx sig_ty thing_inside = do
  let pat_sig_ty = csPatSigType sig_ty
  free_ki_vars <- filterInScopeM (extractCsTyRdrKindVars pat_sig_ty)
  rnImplicitKvOccs free_ki_vars $ \imp_kvs -> do
    let env = RTE ctx RnTypeBody
    (pat_sig_ty', fvs1) <- rnLCsTy env pat_sig_ty
    let sig_names = CsPSRn imp_kvs
        sig_ty' = CsPS sig_names pat_sig_ty'
    (res, fvs2) <- thing_inside sig_ty'
    return (res, fvs1 `plusFV` fvs2)                              

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

-- bindHsQTyVars
-- We require all type variables to be bound (by forall or lambda)
-- All kind variables are implicitly universally quantified (no user quantification)
-- We need 
bindCsTyKiVars
  :: CsDocContext
  -> FreeTyKiVars
  -> ([Name] -> RnM (b, FreeVars))
  -> RnM (b, FreeVars)
bindCsTyKiVars doc all_implicit_occs thing_inside = do
  traceRn "checkMixedVars3" $
    vcat [ text "all_implicit_occs" <+> ppr all_implicit_occs ]

  rnImplicitTvKvOccs all_implicit_occs $ \ all_implicit_nms' -> do
    let all_kv_nms = map (`setNameLoc` bndrs_loc) all_kv_nms'
    traceRn "bindCsKiVars" (ppr all_kv_nms)
    thing_inside all_kv_nms
  where
    bndrs_loc = case map getLocA all_kv_occs of
      [] -> panic "bindCsKiVars/bndrs_loc"
      [loc] -> loc
      loc:locs -> loc `combineSrcSpans` last locs

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

precParseErr :: (OpName, Fixity) -> (OpName, Fixity) -> RnM ()
precParseErr op1@(n1, _) op2@(n2, _)
  | is_unbound n1 || is_unbound n2
  = return ()
  | otherwise
  = panic "addErr $ TcRnPrecedenceParsingError op1 op2"

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
'Free' type variables are things like type synonyms:
they are non quantified in a type sig but they may not yet be in scope.
-}

-- Extract ALL the free kind variables from a CsType.
-- In GHC, order of the result list matters for scoping:
-- The kvs in the result type signature should be last in the list since
-- GHC checks that these are quantified earlier.
-- We don't care; all kvs are implicitly quantified; we don't allow explicit quantification.
-- We list them in the order they appear from left to right. 
extractCsTyRdrTyKiVars :: LCsType Ps -> FreeTyKiVars
extractCsTyRdrTyKiVars ty = extract_lty ty []

extract_lty :: LCsType Ps -> FreeTyKiVars -> FreeTyKiVars
extract_lty (L _ ty) acc = case ty of
  CsForAllTy _ tele ty -> extract_cs_for_all_telescope tele acc
                          $ extract_lty ty []
  CsQualTy _ c ty -> extract_cs_context c
                     $ extract_lty ty acc
  CsTyVar _ ltv -> extract_tv ltv acc
  CsUnboundName _ rdr_name -> extract_unbound_tv rdr_name acc
  CsAppTy _ ty1 ty2 -> extract_lty ty1
                       $ extract_lty ty2
  CsFunTy _ arr ty1 ty2 -> extract_lty ty1
                           $ extract_lty ty2
                           $ extract_cs_arrow arr acc
  CsTupleTy _ tys -> extract_ltys tys acc
  CsSumTy _ tys -> extract_ltys tys acc
  CsOpTy _ ty1 tv ty2 -> extract_tv tv
                         $ extract_lty ty1
                         $ extract_lty ty2 acc
  CsParTy _ ty -> extract_lty ty acc
  CsKindSig _ ty ki -> extract_kind_sig ty ki acc
  CsTyLamTy _ mg -> extract_ty_mg mg acc
  TySectionL _ ty1 ty2 -> extract_lty ty1
                          $ extract_lty ty2 acc
  TySectionR _ ty1 ty2 -> extract_lty ty1
                          $ extract_lty ty2 acc

extract_kind_sig :: LCsType Ps -> LCsKind Ps -> FreeTyKiVars -> FreeTyKiVars
extract_kind_sig ty ki acc = extract_lty ty $ extract_lki ki acc

extract_cs_arrow :: CsArrow Ps -> FreeTyKiVars -> FreeTyKiVars 
extract_cs_arrow (CsArrow _ ki) acc = extract_lki ki acc

extract_cs_for_all_telescope
  :: CsForAllTelescope Ps -> FreeTyKiVars -> FreeTyKiVars -> FreeTyKiVars
extract_cs_for_all_telescope (CsForAll _ bndrs) acc_vars body_fvs =
  extract_cs_tv_bndrs bndrs acc_vars body_fvs

extract_cs_tv_bndrs :: [LCsTyVarBndr Ps] -> FreeTyKiVars -> FreeTyKiVars -> FreeTyKiVars
extract_cs_tv_bndrs tv_bndrs acc_vars body_vars = new_vars ++ acc_vars
  where
    new_vars
      | null tv_bndrs = body_vars
      | otherwise = filterFreeVarsToBind tv_bndr_rdrs $ bndr_vars ++ body_vars

    bndr_vars = extract_cs_tv_bndrs_kvs tv_bndrs
    tv_bndr_rdrs = map csLTyVarLocName tv_bndrs

extract_cs_tv_bndrs_kvs :: [LCsTyVarBndr Ps] -> FreeTyKiVars
extract_cs_tv_bndrs_kvs tv_bndrs =
  foldr extract_lki [] (tv_bndr_kind <$> tv_bndrs)
  where
    tv_bndr_kind (KindedTyVar _ _ k) = k
    tv_bndr_kind (ImpKindedTyVar _ _ k) = k

filterFreeVarsToBind :: FreeTyKiVars -> FreeTyKiVars -> FreeTyKiVars
filterFreeVarsToBind bndrs = filterOut is_in_scope
  where
    is_in_scope locc = any (eqLocated locc) bndrs

extract_cs_context :: LCsContext Ps -> FreeTyKiVars -> FreeTyKiVars
extract_cs_context (L _ ctxt) acc = foldr extract_cs_kdrel acc ctxt

extract_cs_kdrel :: LCsKdRel Ps -> FreeTyKiVars -> FreeTyKiVars
extract_cs_kdrel (L _ rel) acc = case rel of
  CsKdLT _ k1 k2 -> extract_lki k1
                    $ extract_lki k2 acc
  CsKdLTEQ _ k1 k2 -> extract_lki k1
                      $ extract_lki k2 acc

extract_ty_mg :: MatchGroup Ps (LCsType Ps) -> FreeTyKiVars -> FreeTyKiVars
extract_ty_mg (MG _ (L _ alts)) acc = foldr extract_ty_match acc alts

extract_ty_match :: LMatch Ps (LCsType Ps) -> FreeTyKiVars -> FreeTyKiVars
extract_ty_match (L _ (Match _ _ (L _ pats) grhss)) acc =
  let pats_vars = foldr extract_cs_ty_pat [] pats
      rhs_vars = extract_cs_ty_grhss grhss
      pat_bndr_rdrs = map csLTyPatLocName pats
      new_vars = filterFreeVarsToBind pat_bndr_rdrs $ pats_vars ++ rhs_vars
  in new_vars ++ acc

extract_cs_ty_pat :: LPat Ps -> FreeTyKiVars -> FreeTyKiVars
extract_cs_ty_pat (L _ pat) acc = case pat of
  WilPat {} -> acc
  TyVarPat _ tv -> extract_tv tv acc
  ParPat _ lpat -> extract_cs_ty_pat lpat acc
  KdSigPat _ lpat ksig -> extract_cs_ty_pat lpat
                          $ extract_cs_pat_sig_kind ksig acc
  ImpPat _ lpat -> extract_cs_ty_pat lpat acc
  other -> pprPanic "extract_cs_ty_pat" (ppr other)

extract_cs_pat_sig_kind :: CsPatSigKind (NoTc Ps) -> FreeTyKiVars -> FreeTyKiVars
extract_cs_pat_sig_kind (CsPSK _ ki) acc = extract_cs_lki ki acc

extract_cs_ty_grhss :: GRHSs Ps (LCsType Ps) -> FreeTyKiVars
extract_cs_ty_grhss (GRHSs _ grhss)
  = foldr extract_cs_ty_grhs [] grhss

extract_cs_ty_grhs :: LGRHS Ps (LCsType Ps) -> FreeTyKiVars -> FreeTyKiVars
extract_cs_ty_grhs (L _ (GRHS _ [] ty)) acc = extract_lty ty acc
extract_cs_ty_grhs (L _ (GRHS _ stmt _)) = pprPanic "extractCsTyGRHSKindVars" (ppr stmt)

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
