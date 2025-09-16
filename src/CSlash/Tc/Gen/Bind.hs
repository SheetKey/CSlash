{-# LANGUAGE TupleSections #-}

module CSlash.Tc.Gen.Bind where

import {-# SOURCE #-} CSlash.Tc.Gen.Match ( tcLambdaMatches )
import {-# SOURCE #-} CSlash.Tc.Gen.Expr  ( tcExpr )
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
-- import GHC.Tc.Types.Constraint
-- import GHC.Core.Predicate
import CSlash.Core.UsageEnv
-- import GHC.Tc.Gen.HsType
-- import GHC.Tc.Gen.Pat
import CSlash.Tc.Utils.TcMType
-- import GHC.Tc.Instance.Family( tcGetFamInstEnvs )
import CSlash.Tc.Utils.TcType
-- import GHC.Tc.Validity (checkValidType, checkEscapingKind)
import CSlash.Tc.Zonk.TcType
-- import GHC.Core.Reduction ( Reduction(..) )
-- import GHC.Core.Multiplicity
-- import GHC.Core.FamInstEnv( normaliseType )
-- import GHC.Core.Class   ( Class )
-- import GHC.Core.Coercion( mkSymCo )
-- import CSlash.Core.Type (mkStrLitTy, tidyOpenType, mkCastTy)
-- import CSlash.Core.Type.Ppr( pprTyVars )
import CSlash.Core.Kind

-- import CSlash.Builtin.Types ( mkConstraintTupleTy, multiplicityTy, oneDataConTy  )
import CSlash.Builtin.Types.Prim
import CSlash.Unit.Module

import CSlash.Types.SourceText
import CSlash.Types.Id
import CSlash.Types.Var as Var
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env( MkTidyEnv, TyVarEnv, {-mkVarEnv,-} lookupVarEnv )
import CSlash.Types.Name
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
tcLocalBinds = panic "tcLocalBinds"

tcValBinds
  :: TopLevelFlag
  -> [(RecFlag, LCsBinds Rn)]
  -> [LSig Rn]
  -> TcM thing
  -> TcM ([(RecFlag, LCsBinds Tc)], AnyCsWrapper, thing)
tcValBinds top_lvl binds sigs thing_inside = do
  (poly_ids, sig_fn) <- tcTySigs sigs

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
  :: TopLevelFlag
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

tc_group _ _ _ _ _ = panic "unfinished2"

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
            (L bind_loc (FunBind { fun_id = L nm_loc name, fun_body = L body_loc body }))
  = do
  traceTc "tcPolyCheck" (ppr sig)

  mono_name <- newNameAt (nameOccName name) (locA nm_loc)

  (wrap_gen, body')
    <- tcSkolemizeCompleteSig sig $ \invis_pat_tys rho_ty ->
       let mono_id = mkLocalId mono_name rho_ty 
       in tcExtendBinderStack [TcIdBndr mono_id NotTopLevel]
          -- The following is essentially an "inlining" of the
          -- relevant parts of 'tcFunBindMatches', in particular 'tcBody'
          $ setSrcSpanA bind_loc
          -- $ tcScalingUsage UKd -- DO I need to scale here??
          $ setSrcSpanA body_loc
          $ let tc_body :: CsExpr Rn -> TcM (CsExpr Tc)
                tc_body (CsPar x (L loc e)) = setSrcSpanA loc $ do
                  e' <- tc_body e
                  return (CsPar x (L loc e'))

                tc_body e@(CsLam x matches) = do
                  (wrap, matches') <- tcLambdaMatches e matches invis_pat_tys
                                      (mkCheckExpType rho_ty)
                  return $ mkCsWrap wrap $ CsLam x matches'

                tc_body e@(CsTyLam x matches) = do
                  (wrap, matches') <- tcLambdaMatches e matches invis_pat_tys
                                      (mkCheckExpType rho_ty)
                  return $ mkCsWrap wrap $ CsTyLam x matches'

                
                tc_body e = tcExpr e (mkCheckExpType rho_ty)
            in tc_body body

  let poly_id2 = mkLocalId mono_name (varType poly_id)

  mod <- getModule

  let bind' = FunBind { fun_id = L nm_loc poly_id2
                      , fun_body = L body_loc body'
                      , fun_ext = (wrap_gen, []) }

      export = ABE { abe_poly = panic "poly_id"
                   , abe_mono = panic "poly_id2" }

      abs_bind = L bind_loc $ XCsBindsLR
                 $ AbsBinds { abs_tvs = []
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
tcPolyInfer = panic "tcPolyInfer"

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
