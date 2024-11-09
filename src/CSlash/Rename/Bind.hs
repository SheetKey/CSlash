{-# LANGUAGE NamedFieldPuns #-}

module CSlash.Rename.Bind where

-- import {-# SOURCE #-} GHC.Rename.Expr( rnExpr, rnLExpr, rnStmts )

import CSlash.Cs
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad
-- import GHC.Rename.HsType
import CSlash.Rename.Pat
import CSlash.Rename.Names
import CSlash.Rename.Env
import CSlash.Rename.Fixity
-- import GHC.Rename.Utils ( mapFvRn
--                         , checkDupRdrNames
--                         , warnUnusedLocalBinds
--                         , checkUnusedRecordWildcard
--                         , checkDupAndShadowedNames, bindLocalNamesFV
--                         , addNoNestedForallsContextsErr, checkInferredVars )
import CSlash.Driver.DynFlags
import CSlash.Unit.Module
import CSlash.Types.Error
-- import CSlash.Types.FieldLabel
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set
import CSlash.Types.Name.Reader ( RdrName, rdrNameOcc )
import CSlash.Types.SourceFile
import CSlash.Types.SrcLoc as SrcLoc
import CSlash.Data.List.SetOps    ( findDupsEq )
import CSlash.Types.Basic         ( RecFlag(..), TypeOrKind(..) )
import CSlash.Data.Graph.Directed ( SCC(..) )
import CSlash.Data.Bag
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Types.Unique.Set
import CSlash.Data.Maybe          ( orElse )
import CSlash.Data.OrdList
-- import qualified GHC.LanguageExtensions as LangExt

-- import Language.Haskell.Syntax.Basic (FieldLabelString(..))

import Control.Monad
import Data.List          ( partition )
import Data.List.NonEmpty ( NonEmpty(..) )

{- *********************************************************************
*                                                                      *
               Top-level bindings
*                                                                      *
********************************************************************* -}

rnTopBindsLHS :: MiniFixityEnv -> CsValBinds Ps -> RnM (CsValBindsLR Rn Ps)
rnTopBindsLHS fix_env binds = rnValBindsLHS (topRecNameMaker fix_env) binds

{- *********************************************************************
*                                                                      *
                ValBinds
*                                                                      *
********************************************************************* -}

rnValBindsLHS :: NameMaker -> CsValBinds Ps -> RnM (CsValBindsLR Rn Ps)
rnValBindsLHS topP (ValBinds x mbinds sigs) = do
  mbinds' <- mapBagM (wrapLocMA (rnBindLHS topP doc)) mbinds
  return $ ValBinds x mbinds' sigs
  where
    bndrs = collectCsBindsBinders CollNoDictBinders mbinds
    doc = text "In the binding group for:" <+> pprWithCommas ppr bndrs
rnValBindsLHS _ b = pprPanic "rnValBindsLHS" (ppr b)

rnValBindsRHS :: CsSigCtxt -> CsValBindsLR Rn Ps -> RnM (CsValBinds Rn, DefUses)
rnValBindsRHS ctxt (ValBinds _ mbinds sigs) = panic "rnValBindsRHS"
rnValBindsRHS _ b = pprPanic "rnValBindsRHS" (ppr b)

---------------------

rnBindLHS :: NameMaker -> SDoc -> CsBind Ps -> RnM (CsBindLR Rn Ps) 
rnBindLHS name_maker _ bind@(FunBind { fun_id = rdr_name, fun_ext = ext }) = do
  name <- applyNameMaker name_maker rdr_name
  return (bind { fun_id = name, fun_ext = ext })
rnBindLHS _ _ b = pprPanic "rnBindLHS" (ppr b)

{- *********************************************************************
*                                                                      *
          Dependency analysis and other support functions
*                                                                      *
********************************************************************* -}

makeMiniFixityEnv :: [LFixitySig Ps] -> RnM MiniFixityEnv
makeMiniFixityEnv decls = foldM add_one_sig emptyMiniFixityEnv decls
  where
    add_one_sig :: MiniFixityEnv -> LFixitySig Ps -> RnM MiniFixityEnv
    add_one_sig env (L loc (FixitySig ns_spec (L name_loc name) fixity))
      = add_one env (locA loc, locA name_loc, name, fixity, ns_spec)

    add_one env (loc, name_loc, name, fixity, ns_spec) = 
      let fs = occNameFS (rdrNameOcc name)
          fix_item = L loc fixity
      in case search_for_dups ns_spec env fs of
           Nothing -> return $ extend_mini_fixity_env ns_spec env fs fix_item
           Just (L loc' _) -> do
             setSrcSpan loc $ addErrAt name_loc (TcRnMultipleFixityDecls loc' name)
             return env

    search_for_dups ns_spec MFE { mfe_data_level_names, mfe_type_level_names } fs
      = case ns_spec of
          NoNamespaceSpecifier{} -> lookupFsEnv mfe_data_level_names fs
          TypeNamespaceSpecifier{} -> lookupFsEnv mfe_type_level_names fs

    extend_mini_fixity_env ns_spec env@MFE{mfe_data_level_names, mfe_type_level_names} fs fix_item
      = case ns_spec of
          NoNamespaceSpecifier -> env
            { mfe_data_level_names = extendFsEnv mfe_data_level_names fs fix_item }
          TypeNamespaceSpecifier{} -> env
            { mfe_type_level_names = extendFsEnv mfe_type_level_names fs fix_item }

{- ******************************************************
*                                                       *
        Source-code fixity declarations
*                                                       *
****************************************************** -}

rnSrcFixityDecl :: CsSigCtxt -> FixitySig Ps -> RnM (FixitySig Rn)
rnSrcFixityDecl sig_ctxt = panic "rnSrcFixityDecl"
