{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Tc.Module where

import CSlash.Driver.Env
-- import GHC.Driver.Plugins
import CSlash.Driver.DynFlags
import CSlash.Driver.Config.Diagnostic

-- import GHC.Tc.Errors.Hole.Plugin ( HoleFitPluginR (..) )
import CSlash.Tc.Errors.Types
-- import {-# SOURCE #-} GHC.Tc.Gen.Splice ( finishTH, runRemoteModFinalizers )
-- import GHC.Tc.Gen.HsType
-- import GHC.Tc.Validity( checkValidType )
-- import GHC.Tc.Gen.Match
-- import GHC.Tc.Utils.Unify( checkConstraints, tcSubTypeSigma )
import CSlash.Tc.Zonk.Type
-- import GHC.Tc.Gen.Expr
-- import GHC.Tc.Gen.App( tcInferSigma )
import CSlash.Tc.Utils.Monad
-- import GHC.Tc.Gen.Export
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Origin
-- import GHC.Tc.Instance.Family
-- import GHC.Tc.Gen.Annotation
import CSlash.Tc.Gen.Bind
-- import GHC.Tc.Gen.Default
import CSlash.Tc.Utils.Env
-- import GHC.Tc.Gen.Rule
-- import GHC.Tc.Gen.Foreign
-- import GHC.Tc.TyCl.Instance
import CSlash.Tc.Utils.TcMType
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Solver
import CSlash.Tc.CsType
-- import GHC.Tc.Instance.Typeable ( mkTypeableBinds )
-- import GHC.Tc.Utils.Backpack
import CSlash.Tc.Zonk.TcType

-- import GHC.Rename.Bind ( rejectBootDecls )
-- import GHC.Rename.Splice ( rnTopSpliceDecls, traceSplice, SpliceInfo(..) )
-- import GHC.Rename.HsType
-- import GHC.Rename.Expr
-- import GHC.Rename.Fixity ( lookupFixityRn )
import CSlash.Rename.Names
import CSlash.Rename.Env
import CSlash.Rename.Module
-- import GHC.Rename.Doc
-- import GHC.Rename.Utils ( mkNameClashErr )

-- import GHC.Iface.Decl    ( coAxiomToIfaceDecl )
import CSlash.Iface.Env     ( externalizeName )
import CSlash.Iface.Load

-- import CSlash.Builtin.Types ( mkListTy, anyTypeOfKind )
import CSlash.Builtin.Names
import CSlash.Builtin.Utils

import CSlash.Cs --hiding ( FunDep(..) )
import CSlash.Cs.Dump

-- import GHC.Core.PatSyn
-- import GHC.Core.Predicate ( classMethodTy )
-- import GHC.Core.InstEnv
import CSlash.Core.TyCon
import CSlash.Core.DataCon
import CSlash.Core.Type.Rep
import CSlash.Core.Type
-- import GHC.Core.Class
-- import GHC.Core.Coercion.Axiom
-- import GHC.Core.Reduction ( Reduction(..) )
-- import CSlash.Core.Type.Ppr( debugPprType )
-- import GHC.Core.FamInstEnv
--    ( FamInst, pprFamInst, famInstsRepTyCons, orphNamesOfFamInst
--    , famInstEnvElts, extendFamInstEnvList, normaliseType )

import CSlash.Parser.Header       ( mkBuiltInImports )

-- import GHC.IfaceToCore

-- import GHC.Runtime.Context

import CSlash.Utils.Error
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc
import CSlash.Utils.Logger

import CSlash.Types.Error
import CSlash.Types.Name.Reader
import CSlash.Types.Fixity.Env
import CSlash.Types.Id as Id
import CSlash.Types.Id.Info( IdDetails(..) )
import CSlash.Types.Var.Env
import CSlash.Types.TypeEnv
import CSlash.Types.Unique.FM
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set
import CSlash.Types.Avail
import CSlash.Types.Basic hiding( SuccessFlag(..) )
-- import GHC.Types.Annotations
import CSlash.Types.SrcLoc
import CSlash.Types.SourceFile
import CSlash.Types.PkgQual
-- import qualified GHC.LanguageExtensions as LangExt

import CSlash.Unit.External
import CSlash.Unit.Types
import CSlash.Unit.State
import CSlash.Unit.Home
import CSlash.Unit.Module
import CSlash.Unit.Module.Warnings
import CSlash.Unit.Module.ModSummary
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.ModDetails
import CSlash.Unit.Module.Deps

import CSlash.Data.FastString
import CSlash.Data.Maybe
import CSlash.Data.List.SetOps
import CSlash.Data.Bag
-- import qualified GHC.Data.BooleanFormula as BF

import Control.Arrow ( second )
import Control.DeepSeq
import Control.Monad
import Control.Monad.Trans.Writer.CPS
import Data.Data ( Data )
import Data.Functor.Classes ( liftEq )
import Data.List ( sortBy, sort )
import Data.List.NonEmpty ( NonEmpty (..) )
import qualified Data.List.NonEmpty as NE
import Data.Ord
import qualified Data.Set as S
import Data.Foldable ( for_ )
import Data.Traversable ( for )

{- *********************************************************************
*                                                                      *
        Typecheck and rename a module
*                                                                      *
********************************************************************* -}

tcRnModule
  :: CsEnv -> ModSummary -> Bool -> CsParsedModule -> IO (Messages TcRnMessage, Maybe TcGblEnv)
tcRnModule cs_env mod_sum save_rn_syntax
  parsedModule@CsParsedModule{ cpm_module = L loc this_module }
  | RealSrcSpan real_loc _ <- loc
  = withTiming logger (text "Renamer/typechecker" <+> brackets (ppr this_mod)) (const ()) $
    initTc cs_env cs_src save_rn_syntax this_mod real_loc $
    tcRnModuleTcRnM cs_env mod_sum parsedModule pair
  | otherwise
  = return (err_msg `addMessage` emptyMessages, Nothing)
  where
    cs_src = ms_cs_src mod_sum
    logger = cs_logger cs_env
    home_unit = cs_home_unit cs_env
    err_msg = mkPlainErrorMsgEnvelope loc $ TcRnModMissingRealSrcSpan this_mod

    pair :: (Module, SrcSpan)
    pair@(this_mod, _)
      = let L mod_loc mod = csmodName this_module
        in (mkHomeModule home_unit mod, locA mod_loc)

tcRnModuleTcRnM :: CsEnv -> ModSummary -> CsParsedModule -> (Module, SrcSpan) -> TcRn TcGblEnv
tcRnModuleTcRnM cs_env mod_sum parsedModule (this_mod, bi_imp_loc) = do
  let CsParsedModule
        { cpm_module =
            L loc (CsModule _ mod export_ies import_decls local_decls)
        } = parsedModule

      cs_src = ms_cs_src mod_sum

      builtin_imports = mkBuiltInImports (moduleName this_mod) bi_imp_loc import_decls

  when (notNull builtin_imports) $
    traceRn "importing builtins" empty

  let mkImport mod_name = noLocA $ (simpleImportDecl mod_name)
                                   { ideclImportList = Just (Exactly, noLocA []) }

      withReason t imps = map (, text t) imps
      all_imports = withReason "is implicitly imported" builtin_imports
                 ++ withReason "is directly imported" import_decls
  tcg_env <- {-# SCC "tcRnImports" #-}
             tcRnImports cs_env all_imports
  tcg_env1 <- return $ tcg_env { tcg_hdr_info = Just mod }

  setGblEnv tcg_env1 $ do
    traceRn "rn1a" empty
    tcg_env <- case cs_src of
                 CsSrcFile -> {-# SCC "tcRnSrcDecls" #-}
                              tcRnSrcDecls export_ies local_decls
    whenM (goptM Opt_DoCoreLinting) $
      panic "lintGblEnv"
      --lintGblEnv (cs_logger cs_env) (cs_dflags cs_env) tcg_env

    setGblEnv tcg_env $ do
      tcg_env <- getGblEnv
      reportUnusedNames tcg_env cs_src

      tcDump tcg_env
      return tcg_env

{- *********************************************************************
*                                                                      *
                Import declarations
*                                                                      *
********************************************************************* -}

tcRnImports :: CsEnv -> [(LImportDecl Ps, SDoc)] -> TcM TcGblEnv
tcRnImports cs_env import_decls = do
  (rn_imports, rdr_env, imports, pc_info) <- rnImports import_decls
  this_mod <- getModule
  gbl_env <- getGblEnv

  updGblEnv (\gbl -> gbl
              { tcg_rdr_env = tcg_rdr_env gbl `plusGlobalRdrEnv` rdr_env
              , tcg_imports = tcg_imports gbl `plusImportAvails` imports
              , tcg_rn_imports = rn_imports
              , tcg_pc = pc_info
              }) $ do
    traceRn "rn1" (ppr (imp_direct_dep_mods imports))
    failIfErrsM
    getGblEnv

{- *********************************************************************
*                                                                      *
        Type-checking the top level of a module
*                                                                      *
********************************************************************* -}
               
tcRnSrcDecls :: Maybe (LocatedL [LIE Ps]) -> [LCsDecl Ps] -> TcM TcGblEnv
tcRnSrcDecls export_ies decls = do
  (tcg_env, tcl_env, lie) <- tc_rn_src_decls decls

  ------ Simplify constraints ---------
  _ <- {-# SCC "simplifyTop" #-}
    restoreEnvs (tcg_env, tcl_env) $ do
      lie_main <- checkMainType tcg_env
      simplifyTop (lie `andWC` lie_main)

  -- tcg_env <- setGblEnv tcg_env $ mkTypeableBinds

  traceTc "Tc9" empty
  failIfErrsM

  (id_env, binds') <- zonkTcGblEnv tcg_env

  --------- Run finalizers --------------
  let init_tcg_env = tcg_env { tcg_binds = emptyBag
                             , tcg_type_env = tcg_type_env tcg_env `plusTypeEnv` id_env }

  traceTc "Tc11" empty

  --------- Deal with the exports ----------
  tcg_env <- restoreEnvs (tcg_env, tcl_env) $ panic "rnExports export_ies"

  --------- Emit the ':Main.main = runMainIO main' declaration ----------
  tcg_env <- restoreEnvs (tcg_env, tcl_env) $ do
    (tcg_env, lie) <- captureTopConstraints $ checkMain export_ies
    simplifyTop lie
    return tcg_env

  failIfErrsM

  ---------- Final zonking ---------------
  (id_env_mf, binds_mf) <- zonkTcGblEnv tcg_env

  let !final_type_env = tcg_type_env tcg_env `plusTypeEnv` id_env_mf
      tcg_env' = tcg_env { tcg_binds =  binds' `unionBags` binds_mf }

  panic "setGlobalTypeEnv tcg_env' final_type_env"

zonkTcGblEnv :: TcGblEnv -> TcM (TypeEnv, LCsBinds Tc)
zonkTcGblEnv tcg_env@(TcGblEnv { tcg_binds = binds })
  = {-# SCC zonkTopDecls #-}
  setGblEnv tcg_env $ zonkTopDecls binds

tc_rn_src_decls :: [LCsDecl Ps] -> TcM (TcGblEnv, TcLclEnv, WantedConstraints)
tc_rn_src_decls ds = {-# SCC "tc_rn_src_decls" #-} do
  let group = mkGroup ds
  (tcg_env, rn_decls) <- rnTopSrcDecls group

  ((tcg_env, tcl_env), lie1) <- setGblEnv tcg_env
                                $ captureTopConstraints
                                $ tcTopSrcDecls rn_decls
  
  restoreEnvs (tcg_env, tcl_env) $ return (tcg_env, tcl_env, lie1)

{- *********************************************************************
*                                                                      *
        Type-checking the top level of a module (continued)
*                                                                      *
********************************************************************* -}

rnTopSrcDecls :: CsGroup Ps -> TcM (TcGblEnv, CsGroup Rn)
rnTopSrcDecls group = do
  traceRn "rn12" empty
  (tcg_env, rn_decls) <- checkNoErrs $ rnSrcDecls group
  traceRn "rn13" empty
  let tcg_env'
        | Just grp <- tcg_rn_decls tcg_env
        = tcg_env { tcg_rn_decls = Just (appendGroups grp rn_decls) }
        | otherwise
        = tcg_env
  rnDump rn_decls
  return (tcg_env', rn_decls)

tcTopSrcDecls :: CsGroup Rn -> TcM (TcGblEnv, TcLclEnv)
tcTopSrcDecls (CsGroup { cs_typeds = type_ds
                       , cs_valds = cs_val_binds@(XValBindsLR (NValBinds val_binds val_sigs))
                       }) = do
  traceTc "Tc2 (src)" empty

  traceTc "Tc3" empty

  tcg_env <- tcTypeDecls type_ds
  setGblEnv tcg_env $ do
    traceTc "Tc4" empty

    traceTc "Tc5" empty
    tc_envs@(tcg_env, tcl_env) <- tcTopBinds val_binds val_sigs
    restoreEnvs tc_envs $ do
      traceTc "Tc6" empty

      traceTc "Tc7" empty

      traceTc "Tc7a" empty
      let sig_names = mkNameSet (collectCsValBinders CollNoDictBinders cs_val_binds)
                      `minusNameSet` getTypeSigNames val_sigs

          tcg_env' = tcg_env { tcg_sigs = tcg_sigs tcg_env `unionNameSet` sig_names }

      return (tcg_env', tcl_env)

tcTopSrcDecls _ = panic "tcTopSrcDecls: ValBindsIn"

tcTypeDecls :: [TypeGroup Rn] -> TcM TcGblEnv
tcTypeDecls type_decls = do
  tcg_env <- tcTyDecls type_decls
  setGblEnv tcg_env $ do
    failIfErrsM
    return tcg_env

{- *********************************************************************
*                                                                      *
            Checking for 'main'
*                                                                      *
********************************************************************* -}

checkMainType :: TcGblEnv -> TcRn WantedConstraints
checkMainType tcg_env = do
  cs_env <- getTopEnv
  if tcg_mod tcg_env /= mainModIs (cs_HUE cs_env)
    then return emptyWC
    else do rdr_env <- getGlobalRdrEnv
            let dflags = cs_dflags cs_env
                main_occ = getMainOcc dflags
                main_gres = lookupGRE rdr_env (LookupOccName main_occ SameNameSpace)
            case filter isLocalGRE main_gres of
              [] -> return emptyWC
              (_:_:_) -> return emptyWC
              [main_gre] -> panic "checkMainType"

checkMain :: Maybe (LocatedL [LIE Ps]) -> TcM TcGblEnv
checkMain export_ies = do
  panic "checkMain"

getMainOcc :: DynFlags -> OccName
getMainOcc dflags = case mainFunIs dflags of
                      Just fn -> mkVarOccFS (mkFastString fn)
                      Nothing -> mkVarOccFS (fsLit "main")

type RenamedStuff =
  Maybe ( CsGroup Rn
        , [LImportDecl Rn]
        , Maybe [(LIE Rn, Avails)]
        , Maybe (XRec Rn ModuleName)
        )

{- *********************************************************************
*                                                                      *
                Debugging output
      This is what happens when you do -ddump-types
*                                                                      *
********************************************************************* -}

rnDump :: (Outputable a, Data a) => a -> TcRn ()
rnDump rn = dumpOptTcRn Opt_D_dump_rn "Renamer" FormatCSlash (ppr rn)

tcDump :: TcGblEnv -> TcRn ()
tcDump env = do
  panic "tcDump"
