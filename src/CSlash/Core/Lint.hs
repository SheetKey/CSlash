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

import CSlash.Core as Core
import CSlash.Core.FVs
import CSlash.Core.Utils
import CSlash.Core.Stats ( coreBindsStats )
import CSlash.Core.DataCon
import CSlash.Core.Ppr
import CSlash.Core.Type as Type
import CSlash.Core.Predicate( isTyCoVarType )
import CSlash.Core.Kind
import CSlash.Core.UsageEnv
import CSlash.Core.Type.Rep   -- checks validity of types/coercions
import CSlash.Core.Type.Compare ( eqType{-, eqTypes, eqTypeIgnoringMultiplicity, eqForAllVis-} )
import CSlash.Core.Subst
import CSlash.Core.Type.FVs
import CSlash.Core.Type.Ppr
import CSlash.Core.TyCon as TyCon
import CSlash.Core.Unify
-- import CSlash.Core.Opt.Arity    ( typeArity, exprIsDeadEnd )

-- import CSlash.Core.Opt.Monad

import CSlash.Types.Literal
import CSlash.Types.Var as Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Name
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
  -> IO ()
endPassIO logger cfg binds = do
  dumpPassResult logger (ep_dumpCoreSizes cfg) (ep_namePprCtx cfg) mb_flag
                 (renderWithContext defaultSDocContext (ep_prettyPass cfg))
                 (ep_passDetails cfg) binds
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
  -> IO ()
dumpPassResult logger dump_core_sizes name_ppr_ctx mb_flag hdr extra_info binds = do
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
                    ]

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
    all_pairs = mapFst (\case { Core.Id id -> id; _ -> panic "lintCoreBindings'" })
                $ flattenBinds binds

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
type LintedType = Type Zk

lintCoreExpr :: CoreExpr -> LintM (LintedType, UsageEnv)
lintCoreExpr = panic "lintCoreExpr"

lintJoinBndrType :: LintedType -> LintedId -> LintM ()
lintJoinBndrType body_ty bndr = panic "lintJoinBndrType"

{- *********************************************************************
*                                                                      *
                lintCoreArgs
*                                                                      *
********************************************************************* -}

{- *********************************************************************
*                                                                      *
                lintCoreAlts
*                                                                      *
********************************************************************* -}

{- *********************************************************************
*                                                                      *
                lint-types
*                                                                      *
********************************************************************* -}

lintIdBndrs :: TopLevelFlag -> [Id Zk] -> ([LintedId] -> LintM a) -> LintM a
lintIdBndrs top_lvl ids thing_inside = panic "lintIdBnders"

{- *********************************************************************
*                                                                      *
                Types
*                                                                      *
********************************************************************* -}

{- *********************************************************************
*                                                                      *
                Linting Coercions
*                                                                      *
********************************************************************* -}

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
  = RhsOf (Id Zk)
  | TopLevelBindings

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

{-# INLINE ensureEqTys #-}
ensureEqTys :: LintedType -> LintedType -> SDoc -> LintM ()
ensureEqTys ty1 ty2 msg = panic "ensureEqTys"

{- *********************************************************************
*                                                                      *
                Error messages
*                                                                      *
********************************************************************* -}

dumpLoc :: LintLocInfo -> (SrcLoc, SDoc)
dumpLoc (RhsOf v) = (getSrcLoc v, text "In the RHS of" <+> pp_binders [v])
dumpLoc TopLevelBindings = (noSrcLoc, Outputable.empty)

pp_binders :: [Id Zk] -> SDoc
pp_binders bs = sep (punctuate comma (map pp_binder bs))

pp_binder :: Id Zk -> SDoc
pp_binder b = hsep [ppr b, colon, ppr (varType b)]

------------------------------------------------------
--      Other error messages

mkRhsMsg :: Id Zk -> SDoc -> Type Zk -> SDoc
mkRhsMsg binder what ty
  = vcat [ hsep [ text "The type of this binder doesn't match the type of its"
                  <+> what <> colon
                , ppr binder ]
         , hsep [ text "Binder's type:", ppr (varType binder) ]
         , hsep [ text "Rhs type:", ppr ty ] ]

dupVars :: [NonEmpty (Id Zk)] -> SDoc
dupVars vars = hang (text "Duplicate variables brought into scope")
               2 (ppr (map toList vars))

dupExtVars :: [NonEmpty Name] -> SDoc
dupExtVars vars = hang (text "Duplicate top-level variables with the same qualified name")
                  2 (ppr (map toList vars))
