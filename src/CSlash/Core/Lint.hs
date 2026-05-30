{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Lint where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Driver.DynFlags

-- import CSlash.Tc.Utils.TcType ( isFloatingPrimTy )
import CSlash.Unit.Module.ModGuts
import CSlash.Platform

import CSlash.Core as C
import CSlash.Core.FVs
import CSlash.Core.Utils
import CSlash.Core.Stats ( coreBindsStats )
import CSlash.Core.DataCon
import CSlash.Core.Ppr
import CSlash.Core.Type as Type
import CSlash.Core.Predicate( isTyCoVarType )
import CSlash.Core.Kind
import CSlash.Core.Kind.Compare
import CSlash.Core.UsageEnv
import CSlash.Core.Type.Rep   -- checks validity of types/coercions
import CSlash.Core.Type.Compare ( eqType{-, eqTypes, eqTypeIgnoringMultiplicity, eqForAllVis-} )
import CSlash.Core.Subst
import CSlash.Core.Type.FVs
import CSlash.Core.Type.Ppr
import CSlash.Core.TyCon as TyCon
import CSlash.Core.Unify hiding (getSubst)
-- import CSlash.Core.Opt.Arity    ( typeArity, exprIsDeadEnd )

-- import CSlash.Core.Opt.Monad

import CSlash.Types.Literal
import CSlash.Types.Var as Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Name hiding (varName)
import CSlash.Types.Name.Env
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.SrcLoc
import CSlash.Types.Tickish
import CSlash.Types.Unique.FM ( isNullUFM, sizeUFM )
import CSlash.Types.RepType
import CSlash.Types.Basic
import CSlash.Types.Demand      ( {-splitDmdSig,-} isDeadEndDiv )

import CSlash.Builtin.Names
import CSlash.Builtin.Types.Prim

import CSlash.Data.Bag
import CSlash.Data.List.SetOps

import CSlash.Utils.Monad
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Trace
import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.Misc
import CSlash.Utils.Error
import qualified CSlash.Utils.Error as Err
import CSlash.Utils.Logger

import CSlash.Data.Pair
import GHC.Base (oneShot)
import GHC.Data.Unboxed

import Control.Monad
import Data.Foldable      ( for_, toList )
import Data.List.NonEmpty ( NonEmpty(..), groupWith, nonEmpty )
import Data.Maybe
import Data.IntMap.Strict ( IntMap )
import qualified Data.IntMap.Strict as IntMap ( lookup, keys, empty, fromList )

{- *********************************************************************
*                                                                      *
                 Beginning and ending passes
*                                                                      *
********************************************************************* -}

data EndPassConfig = EndPassConfig
  { ep_dumpCoreSizes :: !Bool
  , ep_lintPassResult :: !(Maybe LintPassResultConfig)
  , ep_namePprCtx :: !NamePprCtx
  , ep_dumpFlag :: !(Maybe DumpFlag)
  , ep_prettyPass :: !SDoc
  , ep_passDetails :: !SDoc
  }

endPassIO
  :: Logger
  -> EndPassConfig
  -> CoreProgram
  -> [CoreRule]
  -> IO ()
endPassIO logger cfg binds rules = do
  dumpPassResult logger (ep_dumpCoreSizes cfg) (ep_namePprCtx cfg) mb_flag
                 (renderWithContext defaultSDocContext (ep_prettyPass cfg))
                 (ep_passDetails cfg) binds rules
  for_ (ep_lintPassResult cfg) $ \lp_cfg -> lintPassResult logger lp_cfg binds
  where
    mb_flag = case ep_dumpFlag cfg of
                Just flag | logHasDumpFlag logger flag -> Just flag
                          | logHasDumpFlag logger Opt_D_verbose_core2core -> Just flag
                _ -> Nothing

dumpPassResult
  :: Logger
  -> Bool
  -> NamePprCtx
  -> Maybe DumpFlag
  -> String
  -> SDoc
  -> CoreProgram
  -> [CoreRule]
  -> IO ()
dumpPassResult logger dump_core_sizes name_ppr_ctx mb_flag hdr extra_info binds rules = do
  forM_ mb_flag $ \flag ->
    logDumpFile logger (mkDumpStyle name_ppr_ctx) flag hdr FormatCore dump_doc

  Err.debugTraceMsg logger 2 size_doc
  where
    size_doc = sep [ text "Result size of" <+> text hdr
                   , nest 2 (equals <+> ppr (coreBindsStats binds)) ]

    dump_doc = vcat [ nest 2 extra_info
                    , size_doc
                    , blankLine
                    , if dump_core_sizes
                      then pprCoreBindingsWithSize binds
                      else pprCoreBindings binds
                    , ppUnless (null rules) pp_rules
                    ]
    pp_rules = vcat [ blankLine
                    , text "------ Local rules for imported ids --------"
                    , pprRules rules ]

{- *********************************************************************
*                                                                      *
                 Top-level interfaces
*                                                                      *
********************************************************************* -}
  
data LintPassResultConfig = LintPassResultConfig
  { lpr_diagOpts :: !DiagOpts
  , lpr_platform :: !Platform
  , lpr_makeLintFlags :: !LintFlags
  , lpr_showLintWarnings :: !Bool
  , lpr_passPpr :: !SDoc
  , lpr_localsInScope :: ![Id Zk]
  }

lintPassResult
  :: Logger
  -> LintPassResultConfig
  -> CoreProgram
  -> IO ()
lintPassResult logger cfg binds = do
  let warns_and_errs = lintCoreBindings' (LintConfig { l_diagOpts = lpr_diagOpts cfg
                                                     , l_platform = lpr_platform cfg
                                                     , l_flags = lpr_makeLintFlags cfg
                                                     , l_vars = lpr_localsInScope cfg})
                                         binds
  Err.showPass logger $
    "Core Linted result of" ++
    renderWithContext defaultSDocContext (lpr_passPpr cfg)

  displayLintResults logger
    (lpr_showLintWarnings cfg)
    (lpr_passPpr cfg)
    (pprCoreBindings binds)
    warns_and_errs

displayLintResults
  :: Logger
  -> Bool
  -> SDoc
  -> SDoc
  -> WarnsAndErrs
  -> IO ()
displayLintResults logger display_warnings pp_what pp_pgm (warns, errs)
  | not (isEmptyBag errs)
  = do logMsg logger Err.MCInfo noSrcSpan
         $ withPprStyle defaultDumpStyle
         $ vcat [ lint_banner "errors" pp_what
                , Err.pprMessageBag errs
                , text "*** Offending Program ***"
                , pp_pgm
                , text "*** End of Offense ***" ]
       Err.csExit logger 1

  | not (isEmptyBag warns)
  , log_enable_debug (logFlags logger)
  , display_warnings
  = logMsg logger Err.MCInfo noSrcSpan
    $ withPprStyle defaultDumpStyle
    (lint_banner "warnings" pp_what $$ Err.pprMessageBag (mapBag ($$ blankLine) warns))

  | otherwise
  = return ()

lint_banner :: String -> SDoc -> SDoc
lint_banner string pass = text "*** Core Lint" <+> text string
                          <+> text ": in result of" <+> pass
                          <+> text "***"

lintCoreBindings' :: LintConfig -> CoreProgram -> WarnsAndErrs
lintCoreBindings' cfg binds = initL cfg $ addLoc TopLevelBindings $ do
  checkL (null dups) (dupVars dups)
  checkL (null ext_dups) (dupExtVars ext_dups)
  lintRecBindings TopLevel all_pairs $ \_ -> return ()
  where
    all_pairs = flattenBinds binds

    binders = map fst all_pairs

    (_, dups) = removeDups compare binders

    ext_dups = snd $ removeDupsOn ord_ext $ filter isExternalName $ map Var.varName binders
    ord_ext n = (nameModule n, nameOccName n)


{- *********************************************************************
*                                                                      *
                lintUnfolding
*                                                                      *
********************************************************************* -}

{- *********************************************************************
*                                                                      *
                lintCoreBinding
*                                                                      *
********************************************************************* -}

lintRecBindings
  :: TopLevelFlag
  -> [(Id Zk, CoreExpr)]
  -> ([LintedId] -> LintM a)
  -> LintM (a, [UsageEnv])
lintRecBindings top_lvl pairs thing_inside
  = lintIdBndrs top_lvl bndrs $ \bndrs' -> do
      ues <- zipWithM lint_pair bndrs' rhss
      a <- thing_inside bndrs'
      return (a, ues)
  where
    (bndrs, rhss) = unzip pairs
    lint_pair bndr' rhs = addLoc (RhsOf bndr') $ do
      (rhs_ty, ue) <- lintRhs bndr' rhs
      lintLetBind top_lvl Recursive bndr' rhs rhs_ty
      return ue

lintLetBody :: LintLocInfo -> [LintedId] -> CoreExpr -> LintM (LintedType, UsageEnv)
lintLetBody loc bndrs body = do
  (body_ty, body_ue) <- addLoc loc (lintCoreExpr body)
  mapM_ (lintJoinBndrType body_ty) bndrs
  return (body_ty, body_ue)

lintLetBind
  :: TopLevelFlag
  -> RecFlag
  -> LintedId
  -> CoreExpr
  -> LintedType
  -> LintM ()
lintLetBind top_lvl rec_flag binder rhs rhs_ty = do
  let binder_ty = varType binder
  ensureEqTys binder_ty rhs_ty (mkRhsMsg binder (text "RHS") rhs_ty)

  -- checkL (not (isCoVar binder) || isCoArg rhs)
  --   (mkLetErr binder rhs)

  -- checkL (not (isTopLevel top_lvl && binder_ty `eqType` addrPrimTy)
  --         || exprIsTickedString rhs)
  --   (mkTopNonLitStrMsg binder)

  -- flags <- getLintFlags

  -- case idJoinPointHood binder of
  --   NotJoinPoint -> return ()
  --   JoinPoint arity -> checkL (isValidJoinPointType arity binder_ty)
  --                             (mkInvalidJoinPointMsg binder binder_ty)

  -- when (lf_check_inline_loop_breakers flags
  --       && isStableUnfolding (realIdUnfolding binder)
  --       && isStrongLoopBreaker (idOccInfo binder)
  --       && isInlinePragma (idInlinePragmas binder))
  --   (addWarnL (text "INLINE binder is (non-rule) loop breaker:" <+> ppr binder))

  -- checkL (typeArity (varType binder) >= idArity binder)
  --   (text "idArity" <+> ppr (idArity binder)
  --    <+> text "exceeds typeArity"
  --    <+> ppr (typeArity (varType binder)) <> colon
  --    <+> ppr binder)

  -- case splitDmdSig (idDmdSig binder) of
  --   (demands, result_info) | isDeadEndDiv result_info ->
  --                            if (demands `lengthAtLeast` idArity binder)
  --                            then return ()
  --                            else panic "Hack alert"

  --   _ -> return ()

  -- addLoc (UnfoldingOf binder) $ lintIdUnfolding binder binder_ty (idUnfolding binder)

  -- return ()
  panic "lintLetBind"

lintRhs :: Id Zk -> CoreExpr -> LintM (LintedType, UsageEnv)
lintRhs bndr rhs = panic "lintRhs"

{- *********************************************************************
*                                                                      *
                lintCoreExpr
*                                                                      *
********************************************************************* -}

type LintedId = Id Zk
type LintedTyVar = TyVar Zk
type LintedKiVar = KiVar Zk
type LintedKiCoVar = KiCoVar Zk
type LintedType = Type Zk
type LintedMonoKind = MonoKind Zk
type LintedKind = Kind Zk
type LintedTypeCoercion = TypeCoercion Zk
type LintedKindCoercion = KindCoercion Zk

lintCastExpr :: CoreExpr -> LintedType -> CoreTypeCoercion -> LintM LintedType
lintCastExpr expr expr_ty co = panic "lintCastExpr"

lintCoreExpr :: CoreExpr -> LintM (LintedType, UsageEnv)
lintCoreExpr (Var var) = lintIdOcc var 0
  
lintCoreExpr (Lit lit) = return (literalType lit, emptyUE)

lintCoreExpr (Cast expr co) = do
  (expr_ty, ue) <- markAllJoinsBad (lintCoreExpr expr)
  to_ty <- lintCastExpr expr expr_ty co
  return (to_ty, ue)

lintCoreExpr (Tick tickish expr) = do
  case tickish of
    -- TODO: Breakpoint{} -> panic "Breakpoint"
    _ -> return ()

  markAllJoinsBadIf block_joins $ lintCoreExpr expr
  where
    block_joins = not (tickish `tickishScopesLike` SoftScope)

lintCoreExpr (Let (NonRec _ (Type _)) _) = panic "TypeLet"
lintCoreExpr (Let (NonRec _ (KiCo _)) _) = panic "KiCoLet"
lintCoreExpr (Let (NonRec _ (Kind _)) _) = panic "KindLet"

lintCoreExpr (Let (NonRec bndr rhs) body) = do
  -- (rhs_ty, let_ue) <- lintRhs bndr rhs
  -- res@(_, body_ue) <- lintBinder LetBind (C.Id bndr) $ \(C.Id bndr') -> do
  --   lintLetBind NotTopLevel NonRecursive bndr' rhs rhs_ty
  --   addAliasUE bndr let_ue (lintLetBody (BodyOfLet bndr') [bndr'] body)

  -- checkLinearity body_ue bndr -- TODO: check this is correct (cloning issues?)
  -- return res
  panic "lintCoreExpr Let NonRec"

lintCoreExpr e@(Let (Rec pairs) body) = do
  checkL (not (null pairs)) (emptyRec e)

  let (_, dups) = removeDups compare bndrs
  checkL (null dups) (dupVars dups)

  checkL (all isJoinId bndrs || all (not . isJoinId) bndrs)
    $ mkInconsistentRecMsg bndrs

  ((body_type, body_ue), ues) <-
    lintRecBindings NotTopLevel pairs $ \bndrs' ->
    lintLetBody (BodyOfLetRec bndrs') bndrs' body

  let final_ue = body_ue `addUE` (foldr1 addUE ues)
  forM_ bndrs (checkLinearity final_ue) -- TODO: check this is correct (cloning issues?)

  return (body_type, final_ue)
  where
     bndrs = map fst pairs

lintCoreExpr e@App{} = do
  fun_pair <- lintCoreFun fun (length args)
  app_pair <- lintCoreArgs fun_pair args
  return app_pair
  where
    (fun, args, _) = collectArgsTicks skipTick e
    skipTick t = case collectFunSimple e of
      (Var v) -> etaExpansionTick v t
      _ -> tickishFloatable t

lintCoreExpr (Lam var ki expr)
  = markAllJoinsBad $ lintLambda var $ lintCoreExpr expr

lintCoreExpr (Case scrut var alt_ty alts)
  = lintCaseExpr scrut var alt_ty alts

lintCoreExpr (Type ty) = failWithL (text "Type found as expression" <+> ppr ty)
lintCoreExpr (KiCo co) = failWithL (text "KiCo found as expression" <+> ppr co)
lintCoreExpr (Kind ki) = failWithL (text "Kind found as expression" <+> ppr ki)

lintIdOcc :: CoreId -> Int -> LintM (LintedType, UsageEnv)
lintIdOcc var nargs = addLoc (OccOf var) $ do
  (bndr, linted_bndr_ty) <- lookupIdInScope var
  let occ_ty = varType var
      bndr_ty = varType bndr
  ensureEqTys occ_ty bndr_ty
    $ mkBndrOccTypeMismatchMsg bndr var bndr_ty occ_ty

  checkDeadIdOcc var
  checkJoinOcc var nargs

  usage <- varCallSiteUsage var
  return (linted_bndr_ty, usage)

lintCoreFun :: CoreExpr -> Int -> LintM (LintedType, UsageEnv)
lintCoreFun (Var var) nargs = lintIdOcc var nargs
lintCoreFun (Lam var ki body) nargs
  | nargs /= 0
  = lintLambda var $ lintCoreFun body (nargs - 1)
lintCoreFun expr nargs
  = markAllJoinsBadIf (nargs /= 0)
    $ lintCoreExpr expr

lintLambda :: CoreBndr -> LintM (CoreType, UsageEnv) -> LintM (CoreType, UsageEnv)
lintLambda var lintBody =
  addLoc (LambdaBodyOf var) $
  lintBinder LambdaBind var $ \var' -> do
    (body_ty, ue) <- lintBody
    ue' <- panic "checkLinearity ue var'"
    return (panic "mkLamType var' body_ty, ue'") -- need a function kind 

checkDeadIdOcc :: CoreId -> LintM ()
checkDeadIdOcc id
  | isDeadOcc (idOccInfo id)
  = do in_case <- inCasePat
       checkL in_case (text "Occurrence of a dead Id" <+> ppr id)
  | otherwise
  = return ()

lintJoinBndrType :: LintedType -> LintedId -> LintM ()
lintJoinBndrType body_ty bndr
  | JoinPoint arity <- idJoinPointHood bndr
  , let bndr_ty = varType bndr
  , (bndrs, res) <- splitPiTys bndr_ty
  = checkL (length bndrs >= arity
            && body_ty `eqType` panic "mkPiTypes (drop arity bndrs) res") $
    hang (text "Join point returns different type than body")
    2 (vcat [ text "Join bndr:" <+> ppr bndr <+> colon <+> ppr (varType bndr)
            , text "Join arity:" <+> ppr arity
            , text "Body type:" <+> ppr body_ty ])
  | otherwise
  = return ()

checkJoinOcc :: CoreId -> JoinArity -> LintM ()
checkJoinOcc var n_args
  | JoinPoint join_arity_occ <- idJoinPointHood var
  = do mb_join_arity_bndr <- lookupJoinId var
       case mb_join_arity_bndr of
         NotJoinPoint -> do join_set <- getValidJoins
                            addErrL (text "join set" <+> ppr join_set $$ invalidJoinOcc var)
         JoinPoint join_arity_bndr -> do
           checkL (join_arity_bndr == join_arity_occ) $
             mkJoinBndrOccMismatchMsg var join_arity_bndr join_arity_occ
           checkL (n_args == join_arity_occ) $
             mkBadJumpMsg var join_arity_occ n_args

  | otherwise
  = return ()

checkLinearity :: UsageEnv -> CoreId -> LintM UsageEnv
checkLinearity body_ue lam_var =
  case idKind lam_var of
    ki -> do
      let (lhs, body_ue') = popUE body_ue lam_var
          err_msg = text "Linearity failure in lambda:" <+> ppr lam_var
                    $$ ppr lhs <+> text "</=" <+> ppr ki
      panic "ensureSubUsage lhs ki err_msg"
      return body_ue'

{- *********************************************************************
*                                                                      *
                lintCoreArgs
*                                                                      *
********************************************************************* -}

lintCoreArgs :: (LintedType, UsageEnv) -> [CoreArg] -> LintM (LintedType, UsageEnv)
lintCoreArgs (fun_ty, fun_ue) args = foldM lintCoreArg (fun_ty, fun_ue) args

lintCoreArg :: (LintedType, UsageEnv) -> CoreArg -> LintM (LintedType, UsageEnv)
lintCoreArg (fun_ty, ue) (Type arg_ty) = do
  checkL (not (panic "isCoercionTy arg_ty"))
    (text "Unnecessary coercion-to-type injection:"
     <+> ppr arg_ty)
  arg_ty' <- lintType arg_ty
  res <- lintTyApp fun_ty arg_ty'
  return (res, ue)

lintCoreArg (fun_ty, ue) (KiCo co) = do
  co' <- panic "lintKiCo co"
  res <- lintKiCoApp fun_ty co'
  return (res, ue)

lintCoreArg (fun_ty, ue) (Kind ki) = do
  ki' <- panic "lintKind ki"
  res <- lintKiApp fun_ty ki'
  return (res, ue)

lintCoreArg (fun_ty, fun_ue) arg = do
  (arg_ty, arg_ue) <- markAllJoinsBad $ lintCoreExpr arg
  flags <- getLintFlags
  lintValApp arg fun_ty arg_ty fun_ue arg_ue

lintAltBinders
  :: UsageEnv
  -> CoreId
  -> LintedType
  -> LintedType
  -> [(CoreMonoKind, OutId)]
  -> LintM UsageEnv
lintAltBinders = panic "lintAltBinders"

-- checkCaseLinearity :: UsageEnv -> 
-- checkCaseLinearity

lintTyApp :: LintedType -> LintedType -> LintM LintedType
lintTyApp fun_ty arg_ty
  | Just (tv, body_ty) <- splitForAllTyVar_maybe fun_ty
  = do lintTyKind tv arg_ty
       in_scope <- getInScope
       return (panic "substTyWithInScope in_scope [tv] [arg_ty] body_ty")
  | otherwise
  = failWithL (mkTyAppMsg fun_ty arg_ty)

lintKiCoApp :: LintedType -> LintedKindCoercion -> LintM LintedType
lintKiCoApp fun_ty co
  | Just (cv, body_ty) <- splitForAllForAllKiCoBinder_maybe fun_ty
  , let co_ki = kiCoercionKind co
        cv_ki = varKind cv
  , cv_ki `eqMonoKind` co_ki
  = do in_scope <- getInScope
       let init_subst = mkEmptyTermSubstIS in_scope
           subst = extendKCvSubst init_subst cv co
       return (substTy subst body_ty)
  | otherwise
  = failWithL (mkKiCoAppMsg fun_ty co)

lintKiApp :: LintedType -> LintedMonoKind -> LintM LintedType
lintKiApp fun_ty arg_ki
  | Just (kv, body_ty) <- splitForAllForAllKiBinder_maybe fun_ty
  = do in_scope <- getInScope
       return (panic "substTyWithInScope in_scope [kv] [arg_ki] body_ty")
  | otherwise = panic "unfinished"
  
lintValApp
  :: CoreExpr
  -> LintedType
  -> LintedType
  -> UsageEnv
  -> UsageEnv
  -> LintM (LintedType, UsageEnv)
lintValApp arg fun_ty arg_ty fun_ue arg_ue
  | Just (arg_ty', _, res_ty') <- splitFunTy_maybe fun_ty
  = do ensureEqTys arg_ty' arg_ty (mkAppMsg arg_ty' arg_ty arg)
       let app_ue = panic "addUE fun_ue arg_ue" -- TODO: scaleUE here??
       return (res_ty', app_ue)
  | otherwise
  = failWithL err2
  where
    err2 = mkNonFunAppMsg fun_ty arg_ty arg

lintTyKind :: OutTyVar -> LintedType -> LintM ()
lintTyKind tyvar arg_ty
  = unless (arg_kind `eqMonoKind` tyvar_kind) $
    addErrL (mkKindErrMsg tyvar arg_ty $$ (text "Linted Arg kind:" <+> ppr arg_kind))
  where
    tyvar_kind = varKind tyvar
    arg_kind = typeMonoKind arg_ty

{- *********************************************************************
*                                                                      *
                lintCoreAlts
*                                                                      *
********************************************************************* -}

lintCaseExpr :: CoreExpr -> CoreId -> CoreType -> [CoreAlt] -> LintM (LintedType, UsageEnv)
lintCaseExpr scrut var alt_ty alts = do
  let e = Case scrut var alt_ty alts

  (scrut_ty, scrut_ue) <- markAllJoinsBad $ lintCoreExpr scrut

  let scrut_ki = idKind var

  alt_ty <- addLoc (CaseTy scrut) $ lintValueType alt_ty

  var_ty <- addLoc (IdTy var) $ lintValueType (varType var)

  let isLitPat (Alt (LitAlt _) _ _) = True
      isLitPat _ = False
  checkL (not $ panic "isFloatingPrimTy scrut_ty && any isLitPat alts")
    (text "Lint warning: Scrutinizing floating-point expression with literal pattern in case analysis (see GHC#9238)."
     $$ text "scrut" <+> ppr scrut)

  case tyConAppTyCon_maybe (varType var) of
    Just tycon
      | debugIsOn
      , isAlgTyCon tycon
      , not (panic "isAbstractTyCon tycon")
      , null (tyConDataCons tycon)
      , not (panic "exprIsDeadEnd scrut")
      -> pprTrace "Lint warning: case binder's type has no constructors" (ppr var <+> ppr (varType var)) $
         return ()

    _ -> return ()

  subst <- getSubst
  ensureEqTys var_ty scrut_ty (mkScrutMsg var var_ty scrut_ty subst)

  lintBinder CaseBind (C.Id var) $ \_ -> do
    -- alt_ues <- mapM (lintCoreAlt var scrut_ty scrut_ki alt_ty) alts
    -- let case_ue = panic "what to do??"
    -- checkCaseAlts e scrut_ty alts
    -- return (alt_ty, case_ue)
    panic "unfinished"

checkCaseAlts :: CoreExpr -> LintedType -> [CoreAlt] -> LintM ()
checkCaseAlts e ty alts = do
  panic "checkL (all non_deflt con_alts) (mkNonDefltMsg e)"
  checkL (increasing_tag con_alts) (mkNonIncreasingAltsMsg e)
  checkL (isJust maybe_deflt || not is_infinite_ty || null alts) (nonExhaustiveAltsMsg e)
  where
    (con_alts, maybe_deflt) = panic "findDefault alts"

    increasing_tag (alt1 : rest@(alt2 : _)) = panic "alt1 `ltAlt` alt2 && increasing_tag rest"
    increasing_tag _ = True

    non_deflt (Alt DEFAULT _ _) = False
    non_deflt _ = True

    is_infinite_ty = case tyConAppTyCon_maybe ty of
      Nothing -> False
      Just tycon -> panic "what test here?"

lintAltExpr :: CoreExpr -> LintedType -> LintM UsageEnv
lintAltExpr expr ann_ty = do
  (actual_ty, ue) <- lintCoreExpr expr
  ensureEqTys actual_ty ann_ty (mkCaseAltMsg expr actual_ty ann_ty)
  return ue

lintCoreAlt
  :: CoreId
  -> LintedType
  -> CoreMonoKind
  -> LintedType
  -> CoreAlt
  -> LintM UsageEnv
lintCoreAlt case_bndr _ scrut_kind alt_ty (Alt DEFAULT args rhs) = do
  lintL (null args) (mkDefaultArgsMsg args)
  rhs_ue <- lintAltExpr rhs alt_ty
  let (case_bndr_usage, rhs_ue') = popUE rhs_ue case_bndr
      err_msg = text "Linearity failure in the DEFAULT clause:" <+> ppr case_bndr
                $$ ppr case_bndr_usage <+> text "⊈" <+> ppr scrut_kind
  ensureSubUsage case_bndr_usage scrut_kind err_msg
  return rhs_ue'
  
lintCoreAlt case_bndr scrut_ty _ alt_ty (Alt (LitAlt lit) args rhs) = panic "lintCoreAlt lit"

lintCoreAlt case_bndr scrut_ty _ alt_ty alt@(Alt (DataAlt con) args rhs)
  | Just (tycon, tycon_arg_tys) <- splitTyConApp_maybe scrut_ty
  = addLoc (CaseAlt alt) $ do
      lintL (tycon == dataConTyCon con) (mkBadConMsg tycon con)

      let con_payload_ty = piResultTys (panic "dataConRepType con") tycon_arg_tys
          binderKind (Named _) = panic "existential type"
          binderKind (Anon _ _) = panic "what to do, typemonokind probably"
          kinds = map binderKind $ fst $ panic "splitPiTys con_payload_ty"

      lintBinders CasePatBind (panic "args") $ \args' -> do
        rhs_ue <- lintAltExpr rhs alt_ty
        rhs_ue' <- panic "addLoc (CasePat alt) (lintAltBinders rhs_ue case_bndr scrut_ty"
--                                         con_payload_ty (zipEqual "lintCoreAlt" kinds args'))
        return $ deleteUE rhs_ue' case_bndr

  | otherwise
  = emptyUE <$ addErrL (mkBadAltMsg scrut_ty alt)

lintLinearBinder :: SDoc -> CoreMonoKind -> CoreMonoKind -> LintM ()
lintLinearBinder doc actual_usage described_usage
  = ensureSubMult actual_usage described_usage err_msg
  where
    err_msg = text "Kind of variable does not agree with its context"
              $$ doc
              $$ ppr actual_usage
              $$ text "Annotation:" <+> ppr described_usage

{- *********************************************************************
*                                                                      *
                lint-types
*                                                                      *
********************************************************************* -}

lintBinders :: BindingSite -> [CoreBndr] -> ([CoreBndr] -> LintM a) -> LintM a
lintBinders _ [] linterF = linterF []
lintBinders site (var:vars) linterF = lintBinder site var $ \var' ->
                                      lintBinders site vars $ \vars' ->
                                      linterF (var':vars')

lintBinder :: BindingSite -> CoreBndr -> (CoreBndr -> LintM a) -> LintM a
lintBinder site var linterF = case var of
  -- C.Id var -> lintIdBndr NotTopLevel site var linterF
  _ -> panic "unfinished"

lintIdBndrs :: TopLevelFlag -> [CoreId] -> ([LintedId] -> LintM a) -> LintM a
lintIdBndrs top_lvl ids thing_inside
  = go ids thing_inside
  where
    go [] thing_inside = thing_inside []
    go (id:ids) thing_inside = lintIdBndr top_lvl LetBind id $ \id' ->
                               go ids $ \ids' ->
                               thing_inside (id' : ids')

lintIdBndr :: TopLevelFlag -> BindingSite -> InId -> (OutId -> LintM a) -> LintM a
lintIdBndr top_lvl bind_site id thing_inside = do
  flags <- getLintFlags
  checkL (not (lf_check_global_ids flags) || isLocalId id)
    (text "Non-local Id binder" <+> ppr id)

  checkL (not (isExportedId id) || is_top_lvl)
    (mkNonTopExportedMsg id)

  checkL (not (isExternalName (varName id)) || is_top_lvl)
    (mkNonTopExternalNameMsg id)

  when (isJoinId id) $
    checkL (not is_top_lvl && is_let_bind)
      (mkBadJoinBindMsg id)

  lintL (not (panic "isCoVarType id_ty"))
    (text "Non-CoVar has coercion type" <+> ppr id <+> colon <+> ppr id_ty)

  lintL (not (bind_site == LambdaBind && isEvaldUnfolding (idUnfolding id)))
    (text "Lambda binder with value or OtherCon unfolding.")

  linted_ty <- addLoc (IdTy id) (lintValueType id_ty)

  addInScopeId id linted_ty $
    thing_inside (setVarType id linted_ty)
  where
    id_ty = varType id
    is_top_lvl = isTopLevel top_lvl
    is_let_bind = case bind_site of
                    LetBind -> True
                    _ -> False

{- *********************************************************************
*                                                                      *
                Types
*                                                                      *
********************************************************************* -}

isSimpleKind :: CoreKind -> Bool
isSimpleKind = panic "isSimpleKind"

isSimpleMonoKind :: CoreMonoKind -> Bool
isSimpleMonoKind = panic "isSimpleMonoKind"

lintValueType :: CoreType -> LintM LintedType
lintValueType ty = addLoc (InType ty) $ do
  ty' <- lintType ty
  let sk = typeKind ty'
  lintL (panic "isValueKind sk") $
    hang (text "Ill-kinded type:" <+> ppr ty)
    2 (text "has kind:" <+> ppr sk)
  return ty'

checkTyCon :: CoreTyCon -> LintM ()
checkTyCon _ = return ()

checkTyVarInScope :: CoreSubst -> CoreTyVar -> LintM ()
checkTyVarInScope subst tv
  = checkL (panic "tv `isInScopeTv` subst") $
    hang (text "The type variable" <+> ppr tv)
    2 (text "is out of scope")

lintType :: CoreType -> LintM LintedType
lintType (TyVarTy tv) = do
  subst <- getSubst
  case panic "lookupTyVar subst tv" of
    Just linted_ty -> return linted_ty
    Nothing -> do checkTyVarInScope subst tv
                  return (TyVarTy tv)

lintType ty@(AppTy t1 t2)
  | TyConApp{} <- t1
  = failWithL $ text "TyConApp to the left of AppTy:" <+> ppr ty

  | otherwise
  = do t1' <- lintType t1
       t2' <- lintType t2
       lint_ty_app ty (typeKind t1') [t2']
       return (AppTy t1' t2')             

lintType ty@(TyConApp tc tys)
  | isTypeSynonymTyCon tc
  = do report_unsat <- lf_report_unsat_syns <$> getLintFlags
       lintTySynApp report_unsat ty tc tys

  | Just{} <- panic "tyConAppFunTy_maybe tc tys"
  = failWithL (hang (text "Saturated application of" <+> quotes (ppr tc)) 2 (ppr ty))

  | otherwise
  = do checkTyCon tc
       tys' <- mapM lintType tys
       lint_ty_app ty (coreTyConKind tc) tys'
       return (TyConApp tc tys')

lintType ty@(FunTy ki t1 t2) = do
  t1' <- lintType t1
  t2' <- lintType t2
  ki' <- panic "lintKind ki"
  lintArrow (text "type" <+> quotes (ppr ty)) t1' t2' ki'
  return $ FunTy ki' t1' t2'

lintType (ForAllTy (Bndr tv vis) body_ty)
  -- = lintTvBndr tv $ \tv' -> do
  --     body_ty' <- lintType body_ty
  --     lintForAllBody tv' body_ty'
  --     return $ ForAllTy (Bndr tv' vis) body_ty'
  = panic "lintType"

lintType (ForAllKiCo kcv body_ty)
  -- = lintKCvBndr kcv $ \kcv' -> do
  --     body_ty' <- lintType body_ty
  --     lintForAllKiCoBody kcv' body_ty'
  --     return $ ForAllKiCo kcv' body_ty'
  = panic "lintType"

lintType (BigTyLamTy kv body_ty)
  -- = lintKvBndr kv $ \kv' -> do
  --     body_ty' <- lintType body_ty
  --     lintForAllKiBody kv' body_ty'
  --     return $ BigTyLamTy kv' body_ty'
  = panic "lintType"

lintType (CastTy ty kco) = do
  ty' <- lintType ty
  co' <- panic "lintSimpleKindCoercions kco"
  let ty_ki = typeKind ty'
      co_ki = kicoercionLKind co'
  panic "ensureEqKis ty_ki co_ki (mkCastTyErr ty kco ty_ki co_ki)"
  return (CastTy ty' co')
      
lintType (KindCoercion kco) = do
  kco' <- panic "lintKindCoercion kco"
  return (KindCoercion kco')

lintType _ = panic "lintType"

lintForAllBody :: LintedTyVar -> LintedType -> LintM ()
lintForAllBody tv body_ty = 
  checkValueType body_ty (text "the body of forall:" <+> ppr body_ty)
  
lintForAllKiCoBody :: LintedKiCoVar -> LintedType -> LintM ()
lintForAllKiCoBody kcv body_ty = 
  checkValueType body_ty (text "the body of forall:" <+> ppr body_ty)

lintForAllKiBody :: LintedKiVar -> LintedType -> LintM ()
lintForAllKiBody kv body_ty =
  checkValueType body_ty (text "the body of forall:" <+> ppr body_ty)

lintTySynApp :: Bool -> InType -> CoreTyCon -> [InType] -> LintM LintedType
lintTySynApp report_unsat ty tc tys
  | report_unsat
  , tys `lengthLessThan` tyConArity tc
  = failWithL (hang (text "Un-saturated type application") 2 (ppr ty))

  | ExpandsSyn args rhs tys' <- expandSynTyCon_maybe tc tys
  , let expanded_ty = mkAppTys (piResultTys {-maybe wrong function name-} rhs args) tys'
  = do tys' <- panic "setReportUnsat False (mapM lintType tys)"
       when report_unsat $ do
         _ <- lintType expanded_ty
         return ()

       lint_ty_app ty (coreTyConKind tc) tys'
       return (TyConApp tc tys')

  | otherwise
  = panic "unreachable"

checkValueType :: LintedType -> SDoc -> LintM ()
checkValueType ty doc
  = lintL (isSimpleKind kind)
    (text "Non-Type-like kind when Type-like expected:" <+> ppr kind $$
     text "when checking" <+> doc)
  where kind = typeKind ty

lintArrow :: SDoc -> LintedType -> LintedType -> LintedMonoKind -> LintM ()
lintArrow what t1 t2 ki = do
  unless (isSimpleKind k1) (report (text "argument") k1)
  unless (isSimpleKind k2) (report (text "result") k2)
  unless (isSimpleMonoKind ki) (report (text "function kind") ki)
  where
    k1 = typeKind t1
    k2 = typeKind t2
    report ar k = addErrL (vcat [ hang (text "Ill-kinded" <+> ar)
                                  2 (text "in" <+> what)
                                  , what <+> text "kind:" <+> ppr k ])

lint_ty_app :: CoreType -> LintedKind -> [LintedType] -> LintM ()
lint_ty_app msg_ty k tys
  = lint_app (\msg_ty -> text "type" <+> quotes (ppr msg_ty)) msg_ty k tys

lint_app
  :: Outputable thing => (thing -> SDoc) -> thing -> LintedKind -> [LintedType] -> LintM ()
lint_app mk_msg msg_type !kfn arg_tys = do
  go_app kfn arg_tys
  where
    go_app :: LintedKind -> [CoreType] -> LintM ()
    go_app _ [] = return ()
    go_app _ _ = panic "go_app"
    -- go_app fun_kind@(Mono (FunKi _ kfa kfb)) (ta : tas) = do
    --   let ka = typeKind ta
    --   unless (ka `eqKind` kfa) $
    --     addErrL (lint_app_fail_msg kfn arg_tys mk_msg msg_type
    --              (text "Fun:" <+> (ppr fun_kind $$ ppr ta <+> colon ppr ka)))
    --   go_app kfb tas
    -- go_app (ForAllKi kv kfn) (ta:tas)
    --   | Embed ka <- ta
    --   = do let kind' = substKi (extendKvSubst emptySubst kv ka) kfn
    --        go_app kind' tas

    --   | otherwise
    --   = addErrL (lint_app_fail_msg kfn arg_tys mk_msg msg_type (text "Forall:" <+>
    --                                                             (ppr kv $$ ppr ta)))
    -- go_app kfn ta
    --   = failWithL (lint_app_fail_msg kfn arg_tys mk_msg msg_type (text "Not a fun:"
    --                                                               <+> (ppr kfn $$ ppr ta)))

lint_app_fail_msg
  :: (Outputable a1, Outputable a2) => a1 -> a2 -> (t -> SDoc) -> t -> SDoc -> SDoc
lint_app_fail_msg kfn arg_tys mk_msg msg_type extr
  = vcat [ hang (text "Kind application error in") 2 (mk_msg msg_type)
         , nest 2 (text "Function kind =" <+> ppr kfn)
         , nest 2 (text "Arg types =" <+> ppr arg_tys)
         , panic "extra" ]

{- *********************************************************************
*                                                                      *
        Linting rules
*                                                                      *
********************************************************************* -}

lintCoreRule :: OutId -> LintedType -> CoreRule -> LintM ()
lintCoreRule _ _ BuiltinRule{} = return ()

lintCoreRule fun fun_ty rule@Rule{ ru_name = name, ru_bndrs = bndrs
                                 , ru_args = args, ru_rhs = rhs }
  = lintBinders LambdaBind bndrs $ \_ -> do
      (lhs_ty, _) <- lintCoreArgs (fun_ty, emptyUE) args
      (rhs_ty, _) <- case idJoinPointHood fun of
        JoinPoint join_arity -> do
          checkL (args `lengthIs` join_arity) $ mkBadJoinPointRuleMsg fun join_arity rule
          lintCoreExpr rhs
        _ -> markAllJoinsBad $ lintCoreExpr rhs
      ensureEqTys lhs_ty rhs_ty $
        (rule_doc <+> vcat [ text "lhs type:" <+> ppr lhs_ty
                           , text "rhs type:" <+> ppr rhs_ty
                           , text "fun_ty:" <+> ppr fun_ty ])

      let bad_bndrs = filter is_bad_bndr bndrs

      checkL (null bad_bndrs) (rule_doc <+> text "unbound" <+> ppr bad_bndrs)
  where
    rule_doc = text "Rule" <+> doubleQuotes (ftext name) <> colon

    (lids, ltcvs, ltvs, lkcvs, lkvs) = panic "exprsFreeVars args"
    (rids, rtcvs, rtvs, rkcvs, rkvs) = exprFreeVars rhs

    is_bad_bndr (C.Id bndr) = not (bndr `elemVarSet` lids)
                              && bndr `elemVarSet` rids
    is_bad_bndr (Tv bndr) = not (bndr `elemVarSet` ltvs)
                            && bndr `elemVarSet` rtvs
    is_bad_bndr (KCv bndr) = not (bndr `elemVarSet` lkcvs)
                             && bndr `elemVarSet` rkcvs
                             && isNothing (panic "isReflKiCoVar_maybe bndr")
    is_bad_bndr (Kv bndr) = not (bndr `elemVarSet` lkvs)
                            && bndr `elemVarSet` rkvs

{- *********************************************************************
*                                                                      *
                Linting Coercions
*                                                                      *
********************************************************************* -}

lintSimpleKindCoercion :: InKindCoercion -> LintM LintedKindCoercion
lintSimpleKindCoercion g = panic "lintSimpleKindCoercions"

lintKindCoercion :: InKindCoercion -> LintM LintedKindCoercion
lintKindCoercion = panic "lintKindCoercion"

lintTypeCoercion :: InTypeCoercion -> LintM LintedTypeCoercion
lintTypeCoercion = panic "lintTypeCoercion"

{- *********************************************************************
*                                                                      *
                The Lint Monad
*                                                                      *
********************************************************************* -}

data LintEnv = LE
  { le_flags :: LintFlags
  , le_loc :: [LintLocInfo]
  , le_subst :: CoreSubst
  , le_ids :: VarEnv (Id Zk) (Id Zk, LintedType)
  , le_joins :: IdSet Zk
  , le_ue_aliases :: NameEnv UsageEnv
  , le_platform :: Platform
  , le_diagOpts :: DiagOpts
  }

data LintFlags = LF
  { lf_check_global_ids :: Bool
  , lf_check_inline_loop_breakers :: Bool
  , lf_report_unsat_syns :: Bool
  }

newtype LintM a = LintM' { unLintM :: LintEnv -> WarnsAndErrs -> LResult a }

pattern LintM :: (LintEnv -> WarnsAndErrs -> LResult a) -> LintM a
pattern LintM m <- LintM' m
  where
    LintM m = LintM' (oneShot $ \env -> oneShot $ \we -> m env we)
{-# COMPLETE LintM #-}

instance Functor LintM where
  fmap f (LintM m) = LintM $ \e w -> mapLResult f (m e w)

type WarnsAndErrs = (Bag SDoc, Bag SDoc)

type LResult a = (# MaybeUB a, WarnsAndErrs #)

pattern LResult :: MaybeUB a -> WarnsAndErrs -> LResult a
pattern LResult m w = (# m, w #)
{-# COMPLETE LResult #-}
 
mapLResult :: (a1 -> a2) -> LResult a1 -> LResult a2
mapLResult f (LResult r w) = LResult (fmapMaybeUB f r) w

fromBoxedLResult :: (Maybe a, WarnsAndErrs) -> LResult a
fromBoxedLResult (Just x, errs) = LResult (JustUB x) errs
fromBoxedLResult (Nothing, errs) = LResult NothingUB errs

instance Applicative LintM where
  pure x = LintM $ \_ errs -> LResult (JustUB x) errs
  (<*>) = ap

instance Monad LintM where
  m >>= k = LintM (\env errs ->
                     let res = unLintM m env errs in
                       case res of
                         LResult (JustUB r) errs' -> unLintM (k r) env errs'
                         LResult NothingUB errs' -> LResult NothingUB errs'
                  )

instance MonadFail LintM where
  fail err = failWithL (text err)

getPlatform :: LintM Platform
getPlatform = LintM (\e errs -> (LResult (JustUB $ le_platform e) errs))

data LintLocInfo
  = RhsOf CoreId
  | OccOf CoreId
  | LambdaBodyOf CoreBndr
  | BodyOfLet CoreId
  | BodyOfLetRec [CoreId]
  | CaseAlt CoreAlt
  | CasePat CoreAlt
  | CaseTy CoreExpr
  | IdTy CoreId
  | TopLevelBindings
  | InType CoreType

data LintConfig = LintConfig
  { l_diagOpts :: !DiagOpts
  , l_platform :: !Platform
  , l_flags :: !LintFlags
  , l_vars :: ![Id Zk]
  }

initL :: LintConfig -> LintM a -> WarnsAndErrs
initL cfg m
  = case unLintM m env (emptyBag, emptyBag) of
      LResult (JustUB _) errs -> errs
      LResult NothingUB errs@(_, e) | not (isEmptyBag e) -> errs
                                    | otherwise -> pprPanic
                                                   ("Bug in Lint: a failure occurred " ++
                                                    "without reporting an error message") empty
  where
    ids = l_vars cfg
    env = LE { le_flags = l_flags cfg
             , le_subst = emptySubst
             , le_ids = mkVarEnv [(id, (id, varType id)) | id <- ids]
             , le_joins = emptyVarSet
             , le_loc = []
             , le_ue_aliases = emptyNameEnv
             , le_platform = l_platform cfg
             , le_diagOpts = l_diagOpts cfg
             }

getLintFlags :: LintM LintFlags
getLintFlags = LintM $ \env errs -> fromBoxedLResult (Just (le_flags env), errs)

checkL :: Bool -> SDoc -> LintM ()
checkL True _ = return ()
checkL False msg = failWithL msg

lintL :: Bool -> SDoc -> LintM ()
lintL = checkL

failWithL :: SDoc -> LintM a 
failWithL msg = LintM $ \env (warns, errs) ->
                          fromBoxedLResult (Nothing, (warns, addMsg True env errs msg))

addErrL :: SDoc -> LintM ()
addErrL msg = LintM $ \ env (warns,errs) ->
              fromBoxedLResult (Just (), (warns, addMsg True env errs msg))

addWarnL :: SDoc -> LintM ()
addWarnL msg = LintM $ \ env (warns,errs) ->
              fromBoxedLResult (Just (), (addMsg False env warns msg, errs))

addMsg :: Bool -> LintEnv ->  Bag SDoc -> SDoc -> Bag SDoc
addMsg is_error env msgs msg
  = assertPpr (notNull loc_msgs) msg $
    msgs `snocBag` mk_msg msg
  where
   loc_msgs :: [(SrcLoc, SDoc)]
   loc_msgs = map dumpLoc (le_loc env)

   cxt_doc = vcat [ vcat $ reverse $ map snd loc_msgs
                  , text "Substitution:" <+> ppr (le_subst env) ]
   context | is_error  = cxt_doc
           | otherwise = whenPprDebug cxt_doc

   msg_span = case [ span | (loc,_) <- loc_msgs
                          , let span = srcLocSpan loc
                          , isGoodSrcSpan span ] of
               []    -> noSrcSpan
               (s:_) -> s
   !diag_opts = le_diagOpts env
   mk_msg msg = mkLocMessage (mkMCDiagnostic diag_opts WarningWithoutFlag Nothing) msg_span
                             (msg $$ context)

addLoc :: LintLocInfo -> LintM a -> LintM a
addLoc extra_loc m
  = LintM $ \ env errs ->
    unLintM m (env { le_loc = extra_loc : le_loc env }) errs

inCasePat :: LintM Bool
inCasePat = LintM $ \env errs -> fromBoxedLResult (Just (is_case_pat env), errs)
  where
    is_case_pat LE{ le_loc = CasePat{} : _ } = True
    is_case_pat _ = False

addInScopeId :: CoreId -> LintedType -> LintM a -> LintM a
addInScopeId id linted_ty m
  = LintM $ \env@LE{ le_ids = id_set, le_joins = join_set, le_ue_aliases = aliases } errs ->
    unLintM m (env { le_ids = extendVarEnv id_set id (id, linted_ty)
                   , le_joins = panic "add_joins join_set"
                   , le_ue_aliases = delFromNameEnv aliases (varName id) }) errs

getInScopeIds :: LintM (VarEnv CoreId (CoreId, LintedType))
getInScopeIds = LintM (\env errs -> fromBoxedLResult (Just (le_ids env), errs))

markAllJoinsBad :: LintM a -> LintM a
markAllJoinsBad m
  = LintM $ \env errs -> unLintM m (env { le_joins = emptyVarSet }) errs

markAllJoinsBadIf :: Bool -> LintM a -> LintM a
markAllJoinsBadIf cond m = if cond then markAllJoinsBad m else m

getValidJoins :: LintM (IdSet Zk)
getValidJoins = LintM (\env errs -> fromBoxedLResult (Just (le_joins env), errs))

getSubst :: LintM CoreSubst
getSubst = LintM (\env errs -> fromBoxedLResult (Just (le_subst env), errs))

getUEAliases :: LintM (NameEnv UsageEnv)
getUEAliases = LintM (\env errs -> fromBoxedLResult (Just (le_ue_aliases env), errs))

getInScope :: LintM TermSubstInScope
getInScope
  = LintM (\env errs -> fromBoxedLResult (Just (getTermSubstInScope $ le_subst env), errs))

lookupIdInScope :: CoreId -> LintM (CoreId, LintedType)
lookupIdInScope id_occ = do
  in_scope_ids <- getInScopeIds
  case lookupVarEnv in_scope_ids id_occ of
    Just (id_bndr, linted_ty) -> do
      checkL (not (bad_global id_bndr)) $ global_in_scope id_bndr
      return (id_bndr, linted_ty)
    Nothing -> do
      checkL (not is_local) local_out_of_scope
      return (id_occ, varType id_occ)
  where
    is_local = panic "mustHaveLocalBinding id_occ"
    local_out_of_scope = text "Out of scope:" <+> pprBndr LetBind id_occ
    global_in_scope id_bndr = hang (text "Occurrence is GlobalId, but binding is LocalId")
                              2 $ vcat [ hang (text "occurrence:") 2 $ pprBndr LetBind id_occ
                                       , hang (text "binder:") 2 $ pprBndr LetBind id_bndr ]

    bad_global id_bnd = isGlobalId id_occ
                        && isLocalId id_bnd
                        && not (isWiredIn id_occ)

lookupJoinId :: CoreId -> LintM JoinPointHood
lookupJoinId id = do
  join_set <- getValidJoins
  case lookupVarSet join_set id of
    Just id' -> return (idJoinPointHood id')
    Nothing -> return NotJoinPoint

addAliasUE :: CoreId -> UsageEnv -> LintM a -> LintM a
addAliasUE id ue thing_inside = LintM $ \env errs ->
  let new_ue_aliases = extendNameEnv (le_ue_aliases env) (getName id) ue
  in unLintM thing_inside (env { le_ue_aliases = new_ue_aliases }) errs

varCallSiteUsage :: CoreId -> LintM UsageEnv
varCallSiteUsage id = do
  m <- getUEAliases
  return $ case lookupNameEnv m (getName id) of
    Nothing -> panic "singleUsageUE id"
    Just id_ue -> id_ue

{-# INLINE ensureEqTys #-}
ensureEqTys :: LintedType -> LintedType -> SDoc -> LintM ()
ensureEqTys ty1 ty2 msg = panic "ensureEqTys"

ensureSubUsage :: Usage -> CoreMonoKind -> SDoc -> LintM ()
ensureSubUsage = panic "ensureSubUsage"

ensureSubMult :: CoreMonoKind -> CoreMonoKind -> SDoc -> LintM ()
ensureSubMult actual_mult described_mult err_msg = panic "ensureSubMult"

{- *********************************************************************
*                                                                      *
                Error messages
*                                                                      *
********************************************************************* -}

dumpLoc :: LintLocInfo -> (SrcLoc, SDoc)
dumpLoc (RhsOf v) = (getSrcLoc v, text "In the RHS of" <+> pp_binders [v])
dumpLoc TopLevelBindings = (noSrcLoc, Outputable.empty)
dumpLoc _ = panic "dumpLoc unfinished"

pp_binders :: [Id Zk] -> SDoc
pp_binders bs = sep (punctuate comma (map pp_binder bs))

pp_binder :: Id Zk -> SDoc
pp_binder b = hsep [ppr b, colon, ppr (varType b)]

------------------------------------------------------
--      Messages for case expressions

mkDefaultArgsMsg :: [CoreId] -> SDoc
mkDefaultArgsMsg args
  = hang (text "DEFAULT case with binders") 4 (ppr args)

mkCaseAltMsg :: CoreExpr -> CoreType -> CoreType -> SDoc
mkCaseAltMsg e ty1 ty2
  = hang (text "Type of case alternatives not the same as the annotation on case:")
    4 (vcat [ text "Actual type:" <+> ppr ty1
            , text "Annotation on case:" <+> ppr ty2
            , text "Alt Rhs:" <+> ppr e ])

mkScrutMsg :: CoreId -> CoreType -> CoreType -> CoreSubst -> SDoc
mkScrutMsg var var_ty scrut_ty subst
  = vcat [ text "Result binder in case doesn't match scrutinee:" <+> ppr var
         , text "Result binder type:" <+> ppr var_ty
         , text "Scrutinee type:" <+> ppr scrut_ty
         , hsep [ text "Current subst", ppr subst ] ]

mkNonDefltMsg :: CoreExpr -> SDoc
mkNonDefltMsg e
  = hang (text "Case expression with DEFAULT not at the beginning") 4 (ppr e)

mkNonIncreasingAltsMsg :: CoreExpr -> SDoc
mkNonIncreasingAltsMsg e
  = hang (text "Case expression with badly-ordered alternatives") 4 (ppr e)

nonExhaustiveAltsMsg :: CoreExpr -> SDoc
nonExhaustiveAltsMsg e
  = hang (text "Case expression with non-exhaustive alternatives") 4 (ppr e)

mkBadConMsg :: CoreTyCon -> CoreDataCon -> SDoc
mkBadConMsg tycon datacon
  = vcat [ text "In a case alternative, data constructor isn't in scrutinee type:"
         , text "Scrutinee type constructor:" <+> ppr tycon
         , text "Data con:" <+> ppr datacon ]

mkBadAltMsg :: CoreType -> CoreAlt -> SDoc
mkBadAltMsg scrut_ty alt
  = vcat [ text "Data alternative when scrutinee is not a tycon application"
         , text "Scrutinee type:" <+> ppr scrut_ty
         , text "Alternative:" <+> pprCoreAlt alt ]

------------------------------------------------------
--      Other error messages

mkAppMsg :: CoreType -> CoreType -> CoreExpr -> SDoc
mkAppMsg expected_arg_ty actual_arg_ty arg
  = vcat [ text "Argument value doesn't match argument type:"
         , hang (text "Expected arg type:") 4 (ppr expected_arg_ty)
         , hang (text "Actual arg type:") 4 (ppr actual_arg_ty)
         , hang (text "Arg:") 4 (ppr arg) ]

mkNonFunAppMsg :: CoreType -> CoreType -> CoreExpr -> SDoc
mkNonFunAppMsg fun_ty arg_ty arg
  = vcat [ text "Non-function type in function position"
         , hang (text "Fun type:") 4 (ppr fun_ty)
         , hang (text "Arg type:") 4 (ppr arg_ty)
         , hang (text "Arg:") 4 (ppr arg) ]

mkTyAppMsg :: CoreType -> CoreType -> SDoc
mkTyAppMsg ty arg_ty
  = vcat [text "Illegal type application:"
         , hang (text "Function type:")
           4 (ppr ty <+> colon <+> ppr (typeKind ty))
         , hang (text "Type argument:")
           4 (ppr arg_ty <+> colon <+> ppr (typeKind arg_ty)) ]

mkKiCoAppMsg :: CoreType -> CoreKindCoercion -> SDoc
mkKiCoAppMsg fun_ty co
  = vcat [ text "Illegal kind coercion application:"
         , hang (text "Function type:") 4 (ppr fun_ty)
         , hang (text "Kind coercion argument:")
           4 (ppr co <+> colon <+> ppr (kiCoercionKind co)) ]

emptyRec :: CoreExpr -> SDoc
emptyRec e = hang (text "Empty Rec binding:") 2 (ppr e)

mkRhsMsg :: Id Zk -> SDoc -> Type Zk -> SDoc
mkRhsMsg binder what ty
  = vcat [ hsep [ text "The type of this binder doesn't match the type of its"
                  <+> what <> colon
                , ppr binder ]
         , hsep [ text "Binder's type:", ppr (varType binder) ]
         , hsep [ text "Rhs type:", ppr ty ] ]

mkNonTopExportedMsg :: CoreId -> SDoc
mkNonTopExportedMsg binder
  = hsep [ text "Non-top-level binder is marked as exported:", ppr binder ]

mkNonTopExternalNameMsg :: CoreId -> SDoc
mkNonTopExternalNameMsg binder
  = hsep [ text "Non-top-level binder has an external name:", ppr binder ]

mkKindErrMsg :: CoreTyVar -> CoreType -> SDoc
mkKindErrMsg tyvar arg_ty
  = vcat [ text "Kinds don't match in type application:"
         , hang (text "Type variable:")
           4 (ppr tyvar <+> colon <+> ppr (varKind tyvar))
         , hang (text "Arg type:")
           4 (ppr arg_ty <+> colon <+> ppr (typeKind arg_ty)) ]

mkCastTyErr :: CoreType -> CoreKindCoercion -> CoreKind -> CoreMonoKind -> SDoc
mkCastTyErr = panic "mkCastTyErr"

mkBadJoinBindMsg :: CoreId -> SDoc
mkBadJoinBindMsg var
  = vcat [ text "Bad join point binding:" <+> ppr var
         , text "Join points can be bound only by a non-top-level let" ]

invalidJoinOcc :: CoreId -> SDoc
invalidJoinOcc var
  = vcat [ text "Invalid occurrence of a join variable:" <+> ppr var
         , text "The binder is either not a join point, or not valid here" ]

mkBadJumpMsg :: CoreId -> Int -> Int -> SDoc
mkBadJumpMsg var ar nargs
  = vcat [ text "Join point invoked with wrong number of arguments"
         , text "Join var:" <+> ppr var
         , text "Join arity:" <+> ppr ar
         , text "Number of arguemnts:" <+> int nargs ]

mkInconsistentRecMsg :: [CoreId] -> SDoc
mkInconsistentRecMsg bndrs
  = vcat [ text "Recursive let binders mix values and join points"
         , text "Binders:" <+> hsep (map ppr_with_details bndrs) ]
  where ppr_with_details bndr = ppr bndr <> ppr (idDetails bndr)

mkJoinBndrOccMismatchMsg :: CoreId -> JoinArity -> JoinArity -> SDoc
mkJoinBndrOccMismatchMsg bndr join_arity_bndr join_arity_occ
  = vcat [ text "Mismatch in join point arity between binder and occurrence"
         , text "Var:" <+> ppr bndr
         , text "Arity at binding site:" <+> ppr join_arity_bndr
         , text "Arity at occurrence:" <+> ppr join_arity_occ ]

mkBndrOccTypeMismatchMsg :: CoreId -> CoreId -> LintedType -> LintedType -> SDoc
mkBndrOccTypeMismatchMsg bndr var bndr_ty var_ty
  = vcat [ text "Mismatch in type between binder and occurrence"
         , text "Binder:" <+> ppr bndr <+> colon <+> ppr bndr_ty
         , text "Occurrence:" <+> ppr var <+> colon <+> ppr var_ty
         , text "Before subst:" <+> ppr (varType var) ]

mkBadJoinPointRuleMsg :: JoinId -> JoinArity -> CoreRule -> SDoc
mkBadJoinPointRuleMsg bndr join_arity rule
  = vcat [ text "Join point has rule with wrong number of arguments"
         , text "Var:" <+> ppr bndr
         , text "Join arity:" <+> ppr join_arity
         , text "Rule:" <+> ppr rule ]

dupVars :: [NonEmpty (Id Zk)] -> SDoc
dupVars vars = hang (text "Duplicate variables brought into scope")
               2 (ppr (map toList vars))

dupExtVars :: [NonEmpty Name] -> SDoc
dupExtVars vars = hang (text "Duplicate top-level variables with the same qualified name")
                  2 (ppr (map toList vars))
