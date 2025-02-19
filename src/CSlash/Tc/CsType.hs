module CSlash.Tc.CsType where

import CSlash.Driver.Env
import CSlash.Driver.DynFlags
-- import GHC.Driver.Config.HsToCore

import CSlash.Cs

import CSlash.Tc.Errors.Types
-- import GHC.Tc.TyCl.Build
import CSlash.Tc.Solver ( pushLevelAndSolveEqualities, pushLevelAndSolveEqualitiesX
                        {-, reportUnsolvedEqualities-} )
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Utils.Env
-- import GHC.Tc.Utils.Unify( unifyType, emitResidualTvConstraint )
-- import GHC.Tc.Types.Constraint( emptyWC )
import CSlash.Tc.Validity
-- import GHC.Tc.Zonk.Type
import CSlash.Tc.Zonk.TcType
-- import GHC.Tc.TyCl.Utils
-- import GHC.Tc.TyCl.Class
-- import {-# SOURCE #-} GHC.Tc.TyCl.Instance( tcInstDecls1 )
-- import {-# SOURCE #-} GHC.Tc.Module( checkBootDeclM )
-- import GHC.Tc.Deriv (DerivInfo(..))
import CSlash.Tc.Gen.CsType
import CSlash.Tc.Gen.CsKind
-- import GHC.Tc.Instance.Class( AssocInstInfo(..) )
import CSlash.Tc.Utils.TcMType
import CSlash.Tc.Utils.TcType
-- import GHC.Tc.Instance.Family
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.LclEnv

-- import CSlash.Builtin.Types (oneDataConTy,  unitTy, makeRecoveryTyCon )

-- import GHC.Rename.Env( lookupConstructorFields )

-- import GHC.Core.Multiplicity
-- import GHC.Core.FamInstEnv ( mkBranchedCoAxiom, mkCoAxBranch )
-- import GHC.Core.Coercion
import CSlash.Core.Type
import CSlash.Core.Type.Rep   -- for checkValidRoles
import CSlash.Core.Type.Ppr( pprTyVars )
import CSlash.Core.Kind
-- import GHC.Core.Class
-- import GHC.Core.Coercion.Axiom
import CSlash.Core.TyCon
import CSlash.Core.DataCon
-- import GHC.Core.Unify

import CSlash.Types.Error
import CSlash.Types.Id
import CSlash.Types.Id.Make
import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.Name.Env
import CSlash.Types.SrcLoc
import CSlash.Types.SourceFile
import CSlash.Types.TypeEnv
import CSlash.Types.Unique
import CSlash.Types.Basic

import CSlash.Data.FastString
import CSlash.Data.Maybe
import CSlash.Data.List.SetOps( minusList, equivClasses )

import CSlash.Unit
import CSlash.Unit.Module.ModDetails

import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.Misc

import Control.Monad
import Data.Foldable ( toList, traverse_ )
import Data.Functor.Identity
import Data.List ( partition)
import Data.List.NonEmpty ( NonEmpty(..) )
import qualified Data.List.NonEmpty as NE
import Data.Traversable ( for )
import Data.Tuple( swap )

import Debug.Trace (trace)

{- *********************************************************************
*                                                                      *
            Type checking for type declarations
*                                                                      *
********************************************************************* -}

tcTyDecls :: [TypeGroup Rn] -> TcM TcGblEnv
tcTyDecls typeds_s = checkNoErrs $ fold_env typeds_s
  where
    fold_env :: [TypeGroup Rn] -> TcM TcGblEnv
    fold_env [] = getGblEnv
    fold_env (typeds : typeds_s) = do
      tcg_env <- tcTyGroup typeds
      setGblEnv tcg_env $ fold_env typeds_s

tcTyGroup :: TypeGroup Rn -> TcM TcGblEnv
tcTyGroup (TypeGroup { group_typeds = typeds, group_kisigs = kisigs }) = do
  massertPpr (null kisigs) (ppr kisigs)

  traceTc "---- tcTyGroup ---- {" empty
  traceTc "Decls for" (ppr (map (tydName . unLoc) typeds))

  (tys_with_validity_infos, kindless) <- tcTyDs typeds

  panic "tcTyGroup"

tcTyDs :: [LCsBind Rn] -> TcM ([TyCon], NameSet)
tcTyDs typeds = do
  (tc_tycons, kindless) <- checkNoErrs $ kcTyGroup typeds

  panic "tcTyDs"

{- *********************************************************************
*                                                                      *
                Kind checking
*                                                                      *
********************************************************************* -}

kcTyGroup :: [LCsBind Rn] -> TcM ([PolyTcTyCon], NameSet)
kcTyGroup kindless_decls = do
  mod <- getModule
  traceTc "---- kcTyGroup ---- {" (text "module" <+> ppr mod $$ vcat (map ppr kindless_decls))

  let kindless_names = mkNameSet $ map (tydName . unLoc) kindless_decls

  inferred_tcs <- pushLevelAndSolveEqualities unkSkolAnon [] $ do
    mono_tcs <- inferInitialKinds kindless_decls

    traceTc "kcTyGroup: initial kinds" $ ppr_tc_kinds mono_tcs

    checkNoErrs $ tcExtendKindEnvWithTyCons mono_tcs $
      mapM_ kcLTyDecl kindless_decls

    return mono_tcs

  let inferred_tc_env = mkNameEnv $ map (\tc -> (tyConName tc, tc)) inferred_tcs
  poly_tcs <- concatMapM (generalizeTyDecl inferred_tc_env) kindless_decls

  traceTc "---- kcTyGroup end ---- }" (ppr_tc_kinds poly_tcs)
  return (poly_tcs, kindless_names)
  where
    ppr_tc_kinds tcs = vcat (map pp_tc tcs)
    pp_tc tc = ppr (tyConName tc) <+> colon <+> ppr (tyConKind tc)

type ScopedPairs = [(Name, TcTyVar)]

generalizeTyDecl :: NameEnv MonoTcTyCon -> LCsBind Rn -> TcM [PolyTcTyCon]
generalizeTyDecl inferred_tc_env (L _ decl) = do
  let names_in_this_decl = [tydName decl]

  tc_infos <- liftZonkM $ do
    tc_with_tvs <- mapM skolemize_tc_tycon names_in_this_decl
    mapM zonk_tc_tycon tc_with_tvs

  swizzled_infos <- tcAddDeclCtxt decl (swizzleTcTyConBndrs tc_infos)

  mapAndReportM generalizeTcTyCon swizzled_infos
  where
    skolemize_tc_tycon :: Name -> ZonkM (TcTyCon, SkolemInfo, ScopedPairs)
    skolemize_tc_tycon tc_name = do
      let tc = lookupNameEnv_NF inferred_tc_env tc_name
      skol_info <- mkSkolemInfo (TyConSkol (tyConFlavor tc) tc_name)
      scoped_pairs <- mapSndM (zonkAndSkolemize skol_info) (tcTyConScopedKiVars tc)
      return (tc, skol_info, scoped_pairs)

    zonk_tc_tycon
      :: (TcTyCon, SkolemInfo, ScopedPairs)
      -> ZonkM (TcTyCon, SkolemInfo, ScopedPairs, TcKind)
    zonk_tc_tycon (tc, skol_info, scoped_pairs) = do
      scoped_pairs <- mapSndM zonkTcTyVarToTcTyVar scoped_pairs
      res_kind <- zonkTcKind (tyConResKind tc)
      return (tc, skol_info, scoped_pairs, res_kind)

swizzleTcTyConBndrs
  :: [(TcTyCon, SkolemInfo, ScopedPairs, TcKind)]
  -> TcM [(TcTyCon, SkolemInfo, ScopedPairs, TcKind)]
swizzleTcTyConBndrs tc_infos 
  | all no_swizzle swizzle_pairs
  = do traceTc "Skipping swizzleTcTyConBndrs for" (ppr_infos tc_infos)
       return tc_infos

  | otherwise
  = do checkForDuplicateScopedTyVars swizzle_pairs
       traceTc "swizzleTcTyConBndrs" $
         vcat [ text "before" <+> ppr_infos tc_infos
              , text "swizzle_pairs" <+> ppr swizzle_pairs
              , text "after" <+> ppr_infos swizzled_infos ]
       return swizzled_infos
  where
    swizzled_infos = [ (tc, skol_info, mapSnd swizzle_var scoped_pairs, swizzle_ki kind)
                     | (tc, skol_info, scoped_pairs, kind) <- tc_infos ]

    swizzle_pairs :: [(Name, TypeVar)]
    swizzle_pairs = [ pair | (_, _, pairs, _) <- tc_infos, pair <- pairs ]

    no_swizzle :: (Name, TypeVar) -> Bool
    no_swizzle (nm, tv) = nm == tyVarName tv

    ppr_infos infos = vcat [ ppr tc <+> pprTyVars (map snd pairs) | (tc, _, pairs, _) <- infos ]

    swizzle_env = mkVarEnv (map swap swizzle_pairs)

    swizzleMapper :: TypeMapper () Identity
    swizzleMapper = TypeMapper { tcm_tyvar = swizzle_tv
                               , tcm_tybinder = swizzle_bndr
                               , tcm_tylambinder = swizzle_lam_bndr
                               , tcm_tycon = swizzle_tycon }

    swizzle_tycon tc = pprPanic "swizzle_tc" (ppr tc)

    swizzle_tv _ tv = return $ mkTyVarTy $ swizzle_var tv

    swizzle_bndr :: () -> TypeVar -> ForAllTyFlag -> (() -> TypeVar -> Identity r) -> Identity r
    swizzle_bndr _ tv _ k = k () (swizzle_var tv)

    swizzle_lam_bndr :: () -> TypeVar -> (() -> TypeVar -> Identity r) -> Identity r
    swizzle_lam_bndr _ tv k = k () (swizzle_var tv)

    swizzle_var :: Var -> Var
    swizzle_var v
      | Just nm <- lookupVarEnv swizzle_env v
      = updateVarKind swizzle_ki (v `setVarName` nm)
      | otherwise
      = updateVarKind swizzle_ki v

    (map_type, _) = mapType swizzleMapper
    swizzle_ty ty = runIdentity (map_type ty)

    swizzle_ki ki = trace "swizzle_ki NOT implemented" ki

generalizeTcTyCon :: (MonoTcTyCon, SkolemInfo, ScopedPairs, TcKind) -> TcM PolyTcTyCon
generalizeTcTyCon (tc, skol_info, scoped_prs, tc_res_kind)
  = setSrcSpan (getSrcSpan tc) $ addTyConCtxt tc $ do
      let spec_req_tvs = map snd scoped_prs
          n_spec = length spec_req_tvs - tyConArity tc
          (spec_tvs, req_tvs) = splitAt n_spec spec_req_tvs

      massertPpr (n_spec == 0) $ vcat [ ppr tc
                                      , ppr skol_info
                                      , ppr scoped_prs
                                      , ppr tc_res_kind ]

      traceTc "generalizeTcTyCon: pre zonk"
        $ vcat [ text "tycon =" <+> ppr tc
               , text "spec_req_tvs =" <+> pprTyVars spec_req_tvs
               , text "tc_res_kind =" <+> ppr tc_res_kind ]

      (spec_tvs, req_tvs, tc_res_kind) <- liftZonkM $ do
        spec_tvs <- zonkTcTyVarsToTcTyVars spec_tvs
        req_tvs <- zonkTcTyVarsToTcTyVars req_tvs
        tc_res_kind <- zonkTcKind tc_res_kind
        return (spec_tvs, req_tvs, tc_res_kind)

      traceTc "generalizeTcTyCon: post zonk"
        $ vcat [ text "tycon =" <+> ppr tc
               , text "spec_tvs =" <+> pprTyVars spec_tvs
               , text "req_tvs =" <+> pprTyVars req_tvs
               , text "tc_res_kind =" <+> ppr tc_res_kind ]

      -- let specified_tcbs = mkNamedTyConBinders Specified spec_tvs
      --     required_tcbs = mkAnonTyConBinders req_tvs

      --     all_tcbs = specified_tcbs ++ required_tcbs
      --     flav = tyConFlavor tc

      -- etaExpandAlgTyCon flav skol_info all_tcbs tc_res_kind

      -- let final_tcbs = all_tcbs
      --     tycon = mkTcTyCon (tyConName tc) final

      panic "generalizeTcTyCon unfinished"

tcExtendKindEnvWithTyCons :: [TcTyCon] -> TcM a -> TcM a
tcExtendKindEnvWithTyCons tcs = tcExtendKindEnvList [ (tyConName tc, ATcTyCon tc) | tc <- tcs ]

inferInitialKinds :: [LCsBind Rn] -> TcM [MonoTcTyCon]
inferInitialKinds decls = do
  traceTc "inferInitialKinds {" $ ppr (map (tydName . unLoc) decls)
  tcs <- concatMapM infer_initial_kind decls
  traceTc "inferInitialKinds done }" empty
  return tcs
  where
    infer_initial_kind = addLocM (getInitialKind InitialKindInfer)

getInitialKind :: InitialKindStrategy -> CsBind Rn -> TcM [TcTyCon]
getInitialKind strategy (TyFunBind { tyfun_id = L _ name
                                   , tyfun_body = rhs
                                   , tyfun_ext = (kv_names, _) }) = do
  let ctxt = TySynKindCtxt name
  traceTc "getInitialKind rhs" (ppr rhs)
  tc <- kcDeclHeader strategy name TypeFunFlavor kv_names $
        -- case csTyKindSig rhs of
        --   Just rhs_sig -> TheKind <$> tcLCsKindSig ctxt rhs_sig
        --   Nothing -> return AnyKind
        csTyFunResAndFullKinds ctxt rhs
  return [tc]

getInitialKind _ other = pprPanic "getInitialKind" (ppr other)

csTyFunResAndFullKinds :: UserTypeCtxt -> LCsType Rn -> TcM (Kind, Kind, Arity)
csTyFunResAndFullKinds ctxt lty =
  case unLoc lty of
    CsQualTy _ context ty -> do
      context' <- tcLCsContext context
      (res_kind, full_kind, arity) <- csTyFunResAndFullKinds ctxt ty
      return (addContext context' res_kind, addContext context' full_kind, arity)
      where
        addContext :: [KdRel] -> Kind -> Kind
        addContext context kind = FunKd FKF_C_K (KdContext context) kind
    CsParTy _ ty -> csTyFunResAndFullKinds ctxt ty
    CsKindSig _ _ kind -> do
      kind' <- tcLCsKindSig ctxt kind
      return (kind', kind', 0)
    CsTyLamTy _ mg -> case mg of
      MG _ (L _ [L _ (Match _ _ (L _ pats) (GRHSs _ [L _ (GRHS _ [] body)]))]) -> do
        res_kind <- case csTyKindSig body of
                      Just body_sig -> tcLCsKindSig ctxt body_sig
                      Nothing -> newMetaKindVar
        full_kind <- mkFullKind pats res_kind
        let arity = length pats
        return (res_kind, full_kind, arity)
        where
          mkFullKind :: [LPat Rn] -> Kind -> TcM Kind
          mkFullKind [] k = return k
          mkFullKind (p:ps) res_k = do
            k' <- case unLoc p of
                    TyVarPat _ _ -> newMetaKindVar
                    ParPat _ p' -> mkFullKind (p' : ps) res_k
                    ImpPat _ p' -> mkFullKind (p' : ps) res_k
                    KdSigPat _ _ (CsPSK _ k) -> tcLCsKindSig ctxt k
                    other -> pprPanic "mkFullKind" (ppr other)
            (FunKd FKF_K_K k') <$> mkFullKind ps res_k
      _ -> panic "csTyFunResAndFullKinds"
    _ -> do
      kind <- newMetaKindVar
      return (kind, kind, 0)

-- csTyFunLamBoundArity :: LCsType (CsPass p) -> Arity
-- csTyFunLamBoundArity lty = case unLoc lty of
--   CsQualTy _ _ ty -> csTyFunArity ty
--   CsKindSig _ ty _ -> csTyFunArity ty
--   CsTyLamTy _ mg -> case mg of
--     MG _ [Match _ _ pats _] -> length pats
--     _ -> panic "csTyFunArity"
--   _ -> 0

kcLTyDecl :: LCsBind Rn -> TcM ()
kcLTyDecl (L loc decl) = setSrcSpanA loc $ do
  let tc_name = tydName decl
  tycon <- tcLookupTcTyCon tc_name
  traceTc "kcTyDecl {" (ppr tc_name)
  addErrCtxt (tcMkDeclCtxt decl)
    $ kcTyDecl decl tycon
  traceTc "kcTyDecl done }" (ppr tc_name)

kcTyDecl :: CsBind Rn -> MonoTcTyCon -> TcM ()
kcTyDecl (TyFunBind { tyfun_body = rhs }) tycon
  = tcExtendNameKiVarEnv (tcTyConScopedKiVars tycon) $ 
    let kind = tyConKind tycon
    in discardResult $ tcCheckLCsType rhs (TheKind kind)
kcTyDecl _ _ = panic "kcTyDecl/unreachable"

{- *********************************************************************
*                                                                      *
                Error messages
*                                                                      *
********************************************************************* -}

tcMkDeclCtxt :: CsBind Rn -> SDoc
tcMkDeclCtxt decl = hsep [ text "In the", pprTyDeclFlavor decl
                         , text "declaration for", quotes (ppr (tydName decl)) ]

tcAddDeclCtxt :: CsBind Rn -> TcM a -> TcM a
tcAddDeclCtxt decl thing_inside = addErrCtxt (tcMkDeclCtxt decl) thing_inside

addTyConCtxt :: TyCon -> TcM a -> TcM a
addTyConCtxt tc = addTyConFlavCtxt name flav
  where
    name = getName tc
    flav = tyConFlavor tc
