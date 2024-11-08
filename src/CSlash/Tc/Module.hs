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
-- import GHC.Tc.Zonk.Type
-- import GHC.Tc.Gen.Expr
-- import GHC.Tc.Gen.App( tcInferSigma )
import CSlash.Tc.Utils.Monad
-- import GHC.Tc.Gen.Export
-- import GHC.Tc.Types.Evidence
-- import GHC.Tc.Types.Constraint
-- import GHC.Tc.Types.Origin
-- import GHC.Tc.Instance.Family
-- import GHC.Tc.Gen.Annotation
-- import GHC.Tc.Gen.Bind
-- import GHC.Tc.Gen.Default
-- import GHC.Tc.Utils.Env
-- import GHC.Tc.Gen.Rule
-- import GHC.Tc.Gen.Foreign
-- import GHC.Tc.TyCl.Instance
-- import GHC.Tc.Utils.TcMType
import CSlash.Tc.Utils.TcType
-- import GHC.Tc.Solver
-- import GHC.Tc.TyCl
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

import CSlash.Parser.Header       ( mkPrelImports )

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
tcRnModuleTcRnM cs_env mod_sum parsedModule (this_mod, prel_imp_loc) = do
  let CsParsedModule
        { cpm_module =
            L loc (CsModule _ mod export_ies import_decls local_decls)
        } = parsedModule

      cs_src = ms_cs_src mod_sum

      implicit_prelude = True
      prel_imports = mkPrelImports (moduleName this_mod) prel_imp_loc implicit_prelude import_decls

  when (notNull prel_imports) $
    addDiagnostic TcRnImplicitImportOfPrelude

  let simplifyImport (L _ idecl) =
        ( renameRawPkgQual (cs_unit_env cs_env) (unLoc $ ideclName idecl) NoRawPkgQual
        , reLoc $ ideclName idecl )
  let mkImport mod_name = noLocA $ (simpleImportDecl mod_name)
                                   { ideclImportList = Just (Exactly, noLocA []) }
      withReason t imps = map (, text t) imps
      all_imports = withReason "is implicitly imported" prel_imports
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
  (tcg_env, tcl_env) <- tc_rn_src_decls decls

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
  tcg_env <- restoreEnvs (tcg_env, tcl_env) $ checkMain export_ies

  failIfErrsM

  ---------- Final zonking ---------------
  (id_env_mf, binds_mf) <- zonkTcGblEnv tcg_env

  let !final_type_env = tcg_type_env tcg_env `plusTypeEnv` id_env_mf
      tcg_env' = tcg_env { tcg_binds =  binds' `unionBags` binds_mf }

  panic "setGlobalTypeEnv tcg_env' final_type_env"

zonkTcGblEnv :: TcGblEnv -> TcM (TypeEnv, LCsBinds Tc)
zonkTcGblEnv tcg_env@(TcGblEnv { tcg_binds = binds }) = {-# SCC zonkTopDecls #-}
  setGblEnv tcg_env $ panic "zonkTopDecls binds"

tc_rn_src_decls :: [LCsDecl Ps] -> TcM (TcGblEnv, TcLclEnv)
tc_rn_src_decls ds = {-# SCC "tc_rn_src_decls" #-} do
  let group = mkGroup ds
  (tcg_env, rn_decls) <- rnTopSrcDecls group

  (tcg_env, tcl_env) <- setGblEnv tcg_env $ tcTopSrcDecls rn_decls
  
  restoreEnvs (tcg_env, tcl_env) $ return (tcg_env, tcl_env)

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
  panic "tcRopSrcDecls"
tcTopSrcDecls _ = panic "tcTopSrcDecls: ValBindsIn"

{- *********************************************************************
*                                                                      *
            Checking for 'main'
*                                                                      *
********************************************************************* -}

checkMain :: Maybe (LocatedL [LIE Ps]) -> TcM TcGblEnv
checkMain export_ies = do
  panic "checkMain"

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
rnDump rn = panic "rnDump"

tcDump :: TcGblEnv -> TcRn ()
tcDump env = do
  panic "tcDump"
