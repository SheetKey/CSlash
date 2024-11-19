{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE NamedFieldPuns #-}

module CSlash.Rename.Bind where

import {-# SOURCE #-} CSlash.Rename.Expr ( rnExpr, rnLExpr, rnStmts )

import CSlash.Cs
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad
-- import GHC.Rename.HsType
import CSlash.Rename.Pat
import CSlash.Rename.Names
import CSlash.Rename.Env
import CSlash.Rename.Fixity
import CSlash.Rename.Utils ( mapFvRn
                           , checkDupRdrNames
                           , warnUnusedLocalBinds
                           , checkDupAndShadowedNames, bindLocalNamesFV
                           {-, addNoNestedForallsContextsErr, checkInferredVars-} )
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

{- *********************************************************************
*                                                                      *
              Match
*                                                                      *
********************************************************************* -}

type RnMatchAnnoBody body
  = ( Anno [LocatedA (Match Rn (LocatedA (body Rn)))] ~ SrcSpanAnnL
    , Anno [LocatedA (Match Ps (LocatedA (body Ps)))] ~ SrcSpanAnnL
    , Anno (Match Rn (LocatedA (body Rn))) ~ SrcSpanAnnA
    , Anno (Match Ps (LocatedA (body Ps))) ~ SrcSpanAnnA
    , Anno (GRHS Rn (LocatedA (body Rn))) ~ EpAnnCO
    , Anno (GRHS Ps (LocatedA (body Ps))) ~ EpAnnCO
    , Outputable (body Ps)
    )

rnMatchGroup
  :: RnMatchAnnoBody body
  => CsMatchContextRn
  -> (LocatedA (body Ps) -> RnM (LocatedA (body Rn), FreeVars))
  -> MatchGroup Ps (LocatedA (body Ps))
  -> RnM (MatchGroup Rn (LocatedA (body Rn)), FreeVars)
rnMatchGroup ctxt rnBody (MG { mg_alts = L lm ms, mg_ext = origin }) = do
  when (null ms) $ panic "addErr (TcRnEmptyCase ctxt)"
  (new_ms, ms_fvs) <- mapFvRn (rnMatch ctxt rnBody) ms
  return (mkMatchGroup origin (L lm new_ms), ms_fvs)

rnMatch
  :: RnMatchAnnoBody body
  => CsMatchContextRn
  -> (LocatedA (body Ps) -> RnM (LocatedA (body Rn), FreeVars))
  -> LMatch Ps (LocatedA (body Ps))
  -> RnM (LMatch Rn (LocatedA (body Rn)), FreeVars)
rnMatch ctxt rnBody = wrapLocFstMA (rnMatch' ctxt rnBody)

rnMatch'
  :: RnMatchAnnoBody body
  => CsMatchContextRn
  -> (LocatedA (body Ps) -> RnM (LocatedA (body Rn), FreeVars))
  -> Match Ps (LocatedA (body Ps))
  -> RnM (Match Rn (LocatedA (body Rn)), FreeVars)
rnMatch' ctxt rnBody (Match { m_pats = L l pats, m_grhss = grhss })
 = rnPats ctxt pats $ \pats' -> do
      (grhss', grhss_fvs) <- rnGRHSs ctxt rnBody grhss
      return ( Match { m_ext = noAnn
                    , m_ctxt = ctxt
                    , m_pats = L l pats'
                    , m_grhss = grhss' }
             , grhss_fvs )
      
{- *********************************************************************
*                                                                      *
              Guarded right-hand sides
*                                                                      *
********************************************************************* -}

rnGRHSs
  :: RnMatchAnnoBody body
  => CsMatchContextRn
  -> (LocatedA (body Ps) -> RnM (LocatedA (body Rn), FreeVars))
  -> GRHSs Ps (LocatedA (body Ps))
  -> RnM (GRHSs Rn (LocatedA (body Rn)), FreeVars)
rnGRHSs ctxt rnBody (GRHSs _ grhss) = do
  (grhss', fvGRHSs) <- mapFvRn (rnGRHS ctxt rnBody) grhss
  return (GRHSs emptyComments grhss', fvGRHSs)

rnGRHS
  :: RnMatchAnnoBody body
  => CsMatchContextRn
  -> (LocatedA (body Ps) -> RnM (LocatedA (body Rn), FreeVars))
  -> LGRHS Ps (LocatedA (body Ps))
  -> RnM (LGRHS Rn (LocatedA (body Rn)), FreeVars)
rnGRHS ctxt rnBody = wrapLocFstMA (rnGRHS' ctxt rnBody)

rnGRHS'
  :: RnMatchAnnoBody body
  => CsMatchContextRn
  -> (LocatedA (body Ps) -> RnM (LocatedA (body Rn), FreeVars))
  -> GRHS Ps (LocatedA (body Ps))
  -> RnM (GRHS Rn (LocatedA (body Rn)), FreeVars)
rnGRHS' ctxt rnBody (GRHS _ guards rhs) = do
  let guards_allowed = case ctxt of
                         CaseAlt -> True
                         MultiIfAlt -> True
                         _ -> False
  when (not guards_allowed)
    $ massertPpr (null guards)
    $ text "rhGRHS'" <+> ppr ctxt
      <+> text "has non-empty guards"
      <+> ppr guards
  ((guards', rhs'), fvs) <- rnStmts (PatGuard ctxt) rnExpr guards $ \_ -> rnBody rhs
  return (GRHS noAnn guards' rhs', fvs)
    

{- ******************************************************
*                                                       *
        Source-code fixity declarations
*                                                       *
****************************************************** -}

rnSrcFixityDecl :: CsSigCtxt -> FixitySig Ps -> RnM (FixitySig Rn)
rnSrcFixityDecl sig_ctxt = panic "rnSrcFixityDecl"
