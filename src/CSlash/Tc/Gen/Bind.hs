{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE TupleSections #-}

module CSlash.Tc.Gen.Bind where

import {-# SOURCE #-} CSlash.Tc.Gen.Match ( tcLambdaMatches )
import {-# SOURCE #-} CSlash.Tc.Gen.Expr  ( tcExpr, tcPolyLExpr, tcPolyExpr )
-- import {-# SOURCE #-} GHC.Tc.TyCl.PatSyn ( tcPatSynDecl, tcPatSynBuilderBind )

import CSlash.Types.Tickish ({-CoreTickish,-} GenTickish (..))
-- import GHC.Types.CostCentre (mkUserCC, mkDeclCCFlavour)
import CSlash.Driver.DynFlags
import CSlash.Data.FastString
import CSlash.Cs

-- import GHC.Rename.Bind ( rejectBootDecls )

import CSlash.Tc.Errors.Types
import CSlash.Tc.Gen.Sig
-- import GHC.Tc.Utils.Concrete ( hasFixedRuntimeRep_syntactic )
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.BasicTypes
import CSlash.Tc.Utils.Env
import CSlash.Tc.Utils.Unify
import CSlash.Tc.Solver
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Types.Constraint
-- import GHC.Core.Predicate
import CSlash.Core.UsageEnv
-- import GHC.Tc.Gen.HsType
import CSlash.Tc.Gen.Pat
import CSlash.Tc.Utils.TcMType
-- import GHC.Tc.Instance.Family( tcGetFamInstEnvs )
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Validity (checkValidType)
import CSlash.Tc.Zonk.TcType
-- import GHC.Core.Reduction ( Reduction(..) )
-- import GHC.Core.Multiplicity
-- import GHC.Core.FamInstEnv( normaliseType )
-- import GHC.Core.Class   ( Class )
-- import GHC.Core.Coercion( mkSymCo )
import CSlash.Core.Type
import CSlash.Core.Type.FVs
import CSlash.Core.Type.Compare (eqType)
import CSlash.Core.Type.Tidy (tidyOpenTypeX)
-- import CSlash.Core.Type.Ppr( pprTyVars )
import CSlash.Core.Kind

-- import CSlash.Builtin.Types ( mkConstraintTupleTy, multiplicityTy, oneDataConTy  )
import CSlash.Builtin.Types.Prim
import CSlash.Unit.Module

import CSlash.Types.SourceText
import CSlash.Types.Id
import CSlash.Types.Var as Var
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env( MkTidyEnv, TyVarEnv, AnyTidyEnv, {-mkVarEnv,-} lookupVarEnv )
import CSlash.Types.Name hiding (varName)
import CSlash.Types.Name.Set
import CSlash.Types.Name.Env
import CSlash.Types.SourceFile
import CSlash.Types.SrcLoc

import CSlash.Utils.Error
import CSlash.Utils.Misc
import CSlash.Types.Basic
import CSlash.Types.CompleteMatch
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic
-- import CSlash.Builtin.Names( ipClassName )
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.DSet
import CSlash.Types.Unique.Set

import CSlash.Data.Bag
import CSlash.Data.Graph.Directed
import CSlash.Data.Maybe

import Control.Monad
import Data.Foldable (find)

tcTopBinds :: [(RecFlag, LCsBinds Rn)] -> [LSig Rn] -> TcM (TcGblEnv Tc, TcLclEnv)
tcTopBinds binds sigs = do
  (binds', wrap, (tcg_env, tcl_env)) <- tcValBinds TopLevel binds sigs getEnvs
  massertPpr (isIdCsWrapper wrap)
    (text "Non-identity wrapper at toplevel:" <+> ppr wrap)

  let tcg_env' = tcg_env `addTypecheckedBinds` map snd binds'

  return (tcg_env', tcl_env)

tcLocalBinds :: CsLocalBinds Rn -> TcM thing -> TcM (CsLocalBinds Tc, AnyCsWrapper, thing)

tcLocalBinds (EmptyLocalBinds x) thing_inside = do
  thing <- thing_inside
  return (EmptyLocalBinds x, idCsWrapper, thing)

tcLocalBinds (CsValBinds x (XValBindsLR (NValBinds binds sigs))) thing_inside = do
  (binds', wrapper, thing) <- tcValBinds NotTopLevel binds sigs thing_inside
  return (CsValBinds x (XValBindsLR (NValBinds binds' sigs)), wrapper, thing)

tcLocalBinds (CsValBinds _ (ValBinds {})) _ = panic "tcLocalBinds"

tcValBinds
  :: TopLevelFlag
  -> [(RecFlag, LCsBinds Rn)]
  -> [LSig Rn]
  -> TcM thing
  -> TcM ([(RecFlag, LCsBinds Tc)], AnyCsWrapper, thing)
tcValBinds top_lvl binds sigs thing_inside = do
  (poly_ids, sig_fn) <- tcTySigs top_lvl sigs

  tcExtendSigIds top_lvl poly_ids $ 
    tcBindGroups top_lvl sig_fn binds thing_inside
             
tcBindGroups
  :: TopLevelFlag
  -> TcSigFun
  -> [(RecFlag, LCsBinds Rn)]
  -> TcM thing
  -> TcM ([(RecFlag, LCsBinds Tc)], AnyCsWrapper, thing)
tcBindGroups _ _ [] thing_inside = do
  thing <- thing_inside
  return ([], idCsWrapper, thing)

tcBindGroups top_lvl sig_fn (group:groups) thing_inside = do
  type_env <- getLclTyKiEnv
  let closed = isClosedBndrGroup type_env (snd group)
  (group', outer_wrapper, (groups', inner_wrapper, thing))
    <- tc_group top_lvl sig_fn group closed
       $ tcBindGroups top_lvl sig_fn groups thing_inside
  return (group' ++ groups', outer_wrapper <.> inner_wrapper, thing)

tc_group
  :: forall thing. TopLevelFlag
  -> TcSigFun
  -> (RecFlag, LCsBinds Rn)
  -> IsGroupClosed
  -> TcM thing
  -> TcM ([(RecFlag, LCsBinds Tc)], AnyCsWrapper, thing)

tc_group top_lvl sig_fn (NonRecursive, binds) closed thing_inside = do
  let bind = case binds of
               [bind] -> bind
               [] -> panic "tc_group: empty list of binds"
               _ -> panic "tc_group: NonRecursive binds is not a singleton bag"
  (bind', wrapper, thing) <- tc_single top_lvl sig_fn bind closed thing_inside
  return ([(NonRecursive, bind')], wrapper, thing)

tc_group @thing top_lvl sig_fn (Recursive, binds) closed thing_inside = do
  traceTc "tc_group rec" (pprLCsBinds binds)
  whenIsJust mbFirstPatSyn $ undefined
  (binds1, wrapper, thing) <- go sccs
  return ([(Recursive, binds1)], wrapper, thing)

  where
    mbFirstPatSyn = find (isPatSyn . unLoc) binds
    isPatSyn (FunBind {}) = False
    isPatSyn _ = panic "isPatSyn"

    sccs :: [SCC (LCsBind Rn)]
    sccs = stronglyConnCompFromEdgedVerticesUniq (mkEdges sig_fn binds)

    go :: [SCC (LCsBind Rn)] -> TcM (LCsBinds Tc, AnyCsWrapper, thing)
    go (scc:sccs) = do
      (binds1, ids1) <- tc_scc scc
      ((binds2, inner_wrapper, thing), outer_wrapper)
        <- tcExtendLetEnv top_lvl sig_fn closed ids1 (go sccs)
      return (binds1 ++ binds2, outer_wrapper <.> inner_wrapper, thing)
    go [] = do
      thing <- thing_inside
      return ([], idCsWrapper, thing)

    tc_scc (AcyclicSCC bind) = tc_sub_group NonRecursive [bind]
    tc_scc (CyclicSCC binds) = tc_sub_group Recursive binds

    tc_sub_group rec_tc binds = tcPolyBinds top_lvl sig_fn Recursive rec_tc closed binds

tc_single
  :: TopLevelFlag
  -> TcSigFun
  -> LCsBind Rn
  -> IsGroupClosed
  -> TcM thing
  -> TcM (LCsBinds Tc, AnyCsWrapper, thing)
tc_single top_lvl sig_fn lbind@(L _ FunBind{}) closed thing_inside = do
  (binds1, ids) <- tcPolyBinds top_lvl sig_fn NonRecursive NonRecursive closed [lbind]
  (thing, wrapper) <- tcExtendLetEnv top_lvl sig_fn closed ids thing_inside
  return (binds1, wrapper, thing)

tc_single _ _ _ _ _ = panic "tc_single"

mkEdges :: TcSigFun -> LCsBinds Rn -> [Node Int (LCsBind Rn)]
mkEdges sig_fn binds
  = [ DigraphNode bind key [ key | n <- nonDetEltsUniqSet (bind_fvs (unLoc bind))
                                 , Just key <- [lookupNameEnv key_map n]
                                 , no_sig n ]
    | (bind, key) <- keyd_binds
    ]
  where
    bind_fvs (FunBind { fun_ext = fvs }) = fvs
    bind_fvs _ = panic "bind_fvs"

    no_sig n = not (hasCompleteSig sig_fn n)

    keyd_binds = binds `zip` [0::Int ..]

    key_map = mkNameEnv [ (bndr, key) | (L _ bind, key) <- keyd_binds
                                      , bndr <- collectCsBindBinders CollNoDictBinders bind ]

tcFunBind
  :: UserTypeCtxt
  -> Name
  -> LCsExpr Rn
  -> [ExpPatType] -- all invis
  -> ExpRhoType
  -> TcM (AnyCsWrapper, LCsExpr Tc)
tcFunBind ctxt fun_name (L loc body) invis_pat_tys exp_ty =
  assertPpr (not (any isVisibleExpPatType invis_pat_tys))
            (text "tcFunBind" <+> ppr fun_name <+> ppr invis_pat_tys)
  $ do traceTc "tcFunBind 1"
        $ vcat [ pprUserTypeCtxt ctxt, ppr fun_name, ppr invis_pat_tys, ppr exp_ty ]

       let tc_body  :: CsExpr Rn -> TcM (AnyCsWrapper, CsExpr Tc)
             -- tc_body (CsPar x (L loc e)) = setSrcSpanA loc $ do
             --   e' <- tc_body e
             --   return (CsPar x (L loc e'))

             -- -- Probably only need to check for 'CsTyLam': CsLam can't use the invis_pat_tys
             -- tc_body e@(CsLam x matches) = do
             --   (wrap, matches') <- tcLambdaMatches e matches invis_pat_tys exp_ty
             --   return $ mkCsWrap wrap $ CsLam x matches'

           tc_body e@(CsTyLam x matches) = do
             (wrap, matches') <- tcLambdaMatches e matches invis_pat_tys exp_ty
             return (wrap, CsTyLam x matches')
                
           tc_body e = (idCsWrapper, ) <$> tcPolyExpr e exp_ty
       (wrap, body') <- tc_body body
       return (wrap, L loc body')

tcPolyBinds
  :: TopLevelFlag
  -> TcSigFun
  -> RecFlag
  -> RecFlag
  -> IsGroupClosed
  -> [LCsBind Rn]
  -> TcM (LCsBinds Tc, [TcId])
tcPolyBinds top_lvl sig_fn rec_group rec_tc closed bind_list
  = setSrcSpan loc $ recoverM (recoveryCode binder_names sig_fn) $ do
  traceTc "------------------------------------------------" empty
  traceTc "Bindings for {" (ppr binder_names)
  dflags <- getDynFlags
  let plan = decideGeneralizationPlan dflags top_lvl closed sig_fn bind_list
  traceTc "Generalization plan" (ppr plan)
  result@(_, poly_ids) <- case plan of
    NoGen -> tcPolyNoGen rec_tc sig_fn bind_list
    InferGen -> tcPolyInfer rec_tc sig_fn bind_list
    CheckGen lbind sig -> tcPolyCheck sig lbind

  traceTc "} End of bindigs for"
    $ vcat [ ppr binder_names
           , ppr rec_group
           , vcat [ ppr id <+> ppr (varType id) | id <- poly_ids ] ]

  return result
  where
    binder_names = collectCsBindListBinders CollNoDictBinders bind_list
    loc = foldr1 combineSrcSpans (map (locA . getLoc) bind_list)

recoveryCode :: [Name] -> TcSigFun -> TcM (LCsBinds Tc, [TcId])
recoveryCode binder_names sig_fn = do
  traceTc "tcBindsWithSigs: error recovery" (ppr binder_names)
  let poly_ids = map mk_dummy binder_names
  return ([], poly_ids)
  where
    mk_dummy name
      | Just sig <- sig_fn name
      = completeSigPolyId sig
      | otherwise
      = mkLocalId name forall_a_a

forall_a_a :: AnyType
forall_a_a = panic "forall_a_a"

{- *********************************************************************
*                                                                      *
                tcPolyNoGen
*                                                                      *
********************************************************************* -}

tcPolyNoGen :: RecFlag -> TcSigFun -> [LCsBind Rn] -> TcM (LCsBinds Tc, [TcId])
tcPolyNoGen = panic "tcPolyNoGen"

{- *********************************************************************
*                                                                      *
                tcPolyCheck
*                                                                      *
********************************************************************* -}

tcPolyCheck :: TcCompleteSig -> LCsBind Rn -> TcM (LCsBinds Tc, [TcId])
tcPolyCheck sig@(CSig { sig_bndr = poly_id, sig_ctxt = ctxt })
            (L bind_loc (FunBind { fun_id = L nm_loc name, fun_body = body }))
  = do
  traceTc "tcPolyCheck" (ppr sig)

  mono_name <- newNameAt (nameOccName name) (locA nm_loc)

  (wrap_gen, (wrap_res, body'))
    <- tcSkolemizeCompleteSig sig $ \invis_pat_tys rho_ty ->
       let mono_id = mkLocalId mono_name rho_ty 
       in tcExtendBinderStack [TcIdBndr mono_id NotTopLevel]
          $ setSrcSpanA bind_loc
          $ tcFunBind ctxt mono_name body invis_pat_tys (mkCheckExpType rho_ty)

  let poly_id2 = mkLocalId mono_name (varType poly_id)

  mod <- getModule

  let bind' = FunBind { fun_id = L nm_loc poly_id2
                      , fun_body = body'
                      , fun_ext = (wrap_gen <.> wrap_res, []) }

      export = ABE { abe_wrap = idCsWrapper
                   , abe_poly = poly_id
                   , abe_mono = poly_id2 }

      abs_bind = L bind_loc $ XCsBindsLR
                 $ AbsBinds { abs_kvs = []
                            , abs_tvs = []
                            , abs_exports = [export]
                            , abs_binds = [L bind_loc bind']
                            , abs_sig = True }

  return ([abs_bind], [poly_id])

tcPolyCheck _ _ = panic "tcPolyCheck"

{- *********************************************************************
*                                                                      *
                tcPolyInfer
*                                                                      *
********************************************************************* -}

tcPolyInfer :: RecFlag -> TcSigFun -> [LCsBind Rn] -> TcM (LCsBinds Tc, [TcId])
tcPolyInfer rec_tc tc_sig_fn bind_list = do
  (tclvl, wanted, (binds', mono_infos))
    <- pushLevelAndCaptureConstraints $
       tcMonoBinds rec_tc tc_sig_fn bind_list

  let apply_mr = True -- always monomorphism restriction

  binds' <- manyIfPats binds'

  let name_taus = [ (mbi_poly_name info, varType (mbi_mono_id info))
                  | info <- mono_infos ]
      infer_mode = if apply_mr then ApplyMR else undefined

  traceTc "simplifyInfer call" (ppr tclvl $$ ppr name_taus $$ ppr wanted)

  ((qkvs, qtvs, insoluble), residual)
    <- captureConstraints $ simplifyInfer tclvl infer_mode name_taus wanted
  exports <- checkNoErrs $ mapM (mkExport residual insoluble qkvs qtvs) mono_infos
  

  emitConstraints residual

  loc <- getSrcSpanM
  let poly_ids = abe_poly <$> exports
      abs_bind = L (noAnnSrcSpan loc) $ XCsBindsLR $
                 AbsBinds { abs_kvs = qkvs
                          , abs_tvs = qtvs
                          , abs_exports = exports
                          , abs_binds = binds'
                          , abs_sig = False }
  traceTc "Binding:" (ppr (poly_ids `zip` map varType poly_ids))
  return ([abs_bind], poly_ids)
  where
    manyIfPat bind@(L _ FunBind {}) = return bind
    manyIfPat _ = panic "manyIfPat"

    manyIfPats = traverse manyIfPat

mkExport
  :: WantedTyConstraints
  -> Bool
  -> [TcKiVar] -> [TcTyVar AnyKiVar]
  -> MonoBindInfo
  -> TcM (ABExport Tc)
mkExport residual insoluble qkvs qtvs (MBI { mbi_poly_name = poly_name, mbi_mono_id = mono_id })
  = do mono_ty <- liftZonkM $ zonkTcType (varType mono_id)
       poly_id <- mkInferredPolyId residual insoluble qkvs qtvs poly_name mono_ty

       let poly_ty = varType poly_id
           sel_poly_ty = mkInfSigmaTy qkvs qtvs mono_ty

       traceTc "mkExport"
         $ vcat [ ppr poly_id <+> colon <+> ppr poly_ty
                , ppr sel_poly_ty ]

       wrap <- if sel_poly_ty `eqType` poly_ty
               then return idCsWrapper
               else tcSubTypeSigma (ImpedanceMatching poly_id) sig_ctxt sel_poly_ty poly_ty

       localSigWarn poly_id

       return $ ABE { abe_wrap = wrap
                    , abe_poly = poly_id
                    , abe_mono = mono_id }
  where
    sig_ctxt = InfSigCtxt poly_name

mkInferredPolyId
  :: WantedTyConstraints
  -> Bool
  -> [TcKiVar] -> [TcTyVar AnyKiVar]
  -> Name
  -> AnyType
  -> TcM TcId
mkInferredPolyId residual insoluble qkvs qtvs poly_name mono_ty = checkNoErrs $ do
  (kibinders, tybinders) <- chooseInferredQuantifiers residual (varsOfType mono_ty) qkvs qtvs 
  let inferred_poly_ty = mkBigLamTys kibinders $
                         mkInvisForAllTys tybinders
                         mono_ty
  traceTc "mkInferredPolyId"
    $ vcat [ ppr poly_name, ppr qkvs, ppr qtvs
           , ppr inferred_poly_ty
           , text "insoluble" <+> ppr insoluble ]

  unless insoluble $
    addErrCtxtM (mk_inf_msg poly_name inferred_poly_ty) $ 
      checkValidType (InfSigCtxt poly_name) inferred_poly_ty

  return $ mkLocalId poly_name inferred_poly_ty

chooseInferredQuantifiers
  :: WantedTyConstraints
  -> (MkVarSet (AnyTyVar AnyKiVar), MkVarSet (KiCoVar AnyKiVar), MkVarSet AnyKiVar)
  -> [TcKiVar] -> [TcTyVar AnyKiVar]
  -> TcM ([AnyKiVar], [InvisBinder (AnyTyVar AnyKiVar)])
chooseInferredQuantifiers _ (tau_tvs, tau_kcvs, tau_kvs) qkvs qtvs = return
  ( [ kv
    | tckv <- qkvs
    , let kv = toAnyKiVar tckv
    , kv `elemVarSet` tau_kvs
    ]
  , [ mkVarBinder InferredSpec tv
    | tctv <- qtvs
    , let tv = toAnyTyVar tctv
    , tv `elemVarSet` (tau_tvs `unionVarSet` (toAnyTyVar `mapVarSet` tau_kcvs))
    ]
  )

mk_inf_msg :: Name -> AnyType -> AnyTidyEnv -> ZonkM (AnyTidyEnv, SDoc)
mk_inf_msg poly_name poly_ty tidy_env = do
  (tidy_env1, poly_ty) <- zonkTidyTcType tidy_env poly_ty
  let msg = vcat [ text "When checking the inferred type"
                 , nest 2 $ ppr poly_name <+> colon <+> ppr poly_ty ]
  return (tidy_env1, msg)

localSigWarn :: TcId -> TcM ()
localSigWarn id
  | not (isSigmaTy (varType id)) = return ()
  | otherwise = warnMissingSignatures id

warnMissingSignatures :: TcId -> TcM ()
warnMissingSignatures id = do
  env0 <- liftZonkM $ tcInitTidyEnv
  let (env1, tidy_ty) = tidyOpenTypeX env0 (varType id)
      dia = TcRnPolymorphicBinderMissingSig (varName id) tidy_ty
  addDiagnosticTcM (env1, dia)

{- *********************************************************************
*                                                                      *
                tcMonoBinds
*                                                                      *
********************************************************************* -}

data MonoBindInfo = MBI
  { mbi_poly_name :: Name
  , mbi_mono_id :: TcId
  }

tcMonoBinds
  :: RecFlag
  -> TcSigFun
  -> [LCsBind Rn]
  -> TcM (LCsBinds Tc, [MonoBindInfo])

tcMonoBinds NonRecursive sig_fn [ L b_loc (FunBind { fun_id = L nm_loc name, fun_body = body }) ]
  | Nothing <- sig_fn name
  = setSrcSpanA b_loc $ do
      ((co_fn, body'), rhs_ty') <- tcInfer $ \exp_ty ->
        tcExtendBinderStack [TcIdBndr_ExpType name exp_ty NotTopLevel] $ 
          tcFunBind (InfSigCtxt name) name body [] exp_ty
      mono_id <- newLetBndr name rhs_ty'

      return ( singleton $ L b_loc $ FunBind { fun_id = L nm_loc mono_id
                                             , fun_body = body'
                                             , fun_ext = (co_fn, []) }
             , [MBI { mbi_poly_name = name
                    , mbi_mono_id = mono_id }] )

tcMonoBinds _ sig_fn binds = do
  tc_binds <- mapM (wrapLocMA (tcLhs sig_fn)) binds
  let mono_infos = getMonoBindInfo tc_binds
      rhs_id_env = [ (name, mono_id)
                   | MBI { mbi_poly_name = name
                         , mbi_mono_id = mono_id } <- mono_infos ]
  traceTc "tcMonoBinds"
    $ vcat [ ppr n <+> ppr id <+> ppr (varType id)
           | (n, id) <- rhs_id_env ]
  binds' <- tcExtendRecIds rhs_id_env $
            mapM (wrapLocMA tcRhs) tc_binds
  return (binds', mono_infos)

data TcMonoBind
  = TcFunBind MonoBindInfo SrcSpan (LCsExpr Rn)

tcLhs :: TcSigFun -> CsBind Rn -> TcM TcMonoBind
tcLhs sig_fn (FunBind { fun_id = L nm_loc name, fun_body = body })
  | Just _ <- sig_fn name
  = pprPanic "tcLhs name has sig" (ppr name)
  | otherwise
  = do mono_ty <- asAnyTyKi <$> newOpenFlexiTyVarTy
       mono_id <- newLetBndr name mono_ty
       let mono_info = MBI { mbi_poly_name = name
                           , mbi_mono_id = mono_id }
       return $ TcFunBind mono_info (locA nm_loc) body
tcLhs _ (TCVarBind { tcvar_ext = x }) = dataConCantHappen x
tcLhs _ other = pprPanic "tcLhs" (ppr other)

tcRhs :: TcMonoBind -> TcM (CsBind Tc)
tcRhs (TcFunBind info@(MBI { mbi_mono_id = mono_id }) loc body)
  = tcExtendIdBinderStackForRhs [info] $ do
      let mono_ty = varType mono_id
          mono_name = varName mono_id
      traceTc "tcRhs: fun bind" (ppr mono_id $$ ppr mono_ty)
      (co_fn, body') <- tcFunBind (InfSigCtxt mono_name) mono_name
                                  body [] (mkCheckExpType mono_ty)
      return (FunBind { fun_id = L (noAnnSrcSpan loc) mono_id
                      , fun_body = body'
                      , fun_ext = (co_fn, []) })
-- tcRhs other = pprPanic "tcRhs" (ppr other)

tcExtendIdBinderStackForRhs :: [MonoBindInfo] -> TcM a -> TcM a
tcExtendIdBinderStackForRhs infos thing_inside
  = tcExtendBinderStack [ TcIdBndr mono_id NotTopLevel
                        | MBI { mbi_mono_id = mono_id } <- infos]
    thing_inside

getMonoBindInfo :: [LocatedA TcMonoBind] -> [MonoBindInfo]
getMonoBindInfo tc_binds = foldr (get_info . unLoc) [] tc_binds
  where
    get_info (TcFunBind info _ _) rest = info : rest

{- *********************************************************************
*                                                                      *
                Generalisation
*                                                                      *
********************************************************************* -}

data GeneralizationPlan
  = NoGen
  | InferGen
  | CheckGen (LCsBind Rn) TcCompleteSig

instance Outputable GeneralizationPlan where
  ppr NoGen = text "NoGen"
  ppr InferGen = text "InferGen"
  ppr (CheckGen _ s) = text "CheckGen" <+> ppr s

decideGeneralizationPlan
  :: DynFlags -> TopLevelFlag -> IsGroupClosed -> TcSigFun -> [LCsBind Rn] -> GeneralizationPlan
decideGeneralizationPlan dflags top_lvl closed sig_fn lbinds
  | Just (bind, sig) <- one_funbind_with_sig = CheckGen bind sig
  | generalize_binds = InferGen
  | otherwise = NoGen
  where
    generalize_binds
      | isTopLevel top_lvl = True
      | IsGroupClosed _ True <- closed = True
      | otherwise = False -- MonoLocalBinds

    one_funbind_with_sig
      | [lbind@(L _ (FunBind { fun_id = v }))] <- lbinds
      , Just (TcIdSig sig) <- sig_fn (unLoc v) 
      = Just (lbind, sig)
      | otherwise
      = Nothing

isClosedBndrGroup :: TcTyKiEnv -> [LCsBind Rn] -> IsGroupClosed
isClosedBndrGroup type_env binds = IsGroupClosed fv_env type_closed
  where
    type_closed = allUFM (nameSetAll is_closed_type_id) fv_env

    fv_env :: NameEnv NameSet
    fv_env = mkNameEnv $ concatMap (bindFvs . unLoc) binds

    bindFvs :: CsBindLR Rn Rn -> [(Name, NameSet)]
    bindFvs (FunBind { fun_id = L _ f, fun_ext = fvs })
      = let open_fvs = get_open_fvs fvs
        in [(f, open_fvs)]
    bindFvs _ = panic "bindFvs"

    get_open_fvs fvs = filterNameSet (not . is_closed) fvs

    is_closed :: Name -> ClosedTypeId
    is_closed name
      | Just thing <- lookupNameEnv type_env name
      = case thing of
          AGlobal {} -> True
          ATcId { tct_info = ClosedLet } -> True
          _ -> False

      | otherwise
      = True

    is_closed_type_id :: Name -> ClosedTypeId
    is_closed_type_id name
      | Just thing <- lookupNameEnv type_env name
      = case thing of
          ATcId { tct_info = NonClosedLet _ cl } -> cl
          ATcId { tct_info = NotLetBound } -> False
          ATyVar {} -> False
          AKiVar {} -> False
          _ -> pprPanic "is_closed_id" (ppr name)

      | otherwise
      = True
