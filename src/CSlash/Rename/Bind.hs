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
rnValBindsRHS ctxt (ValBinds _ mbinds sigs) = do
  (sigs', sig_fvs) <- renameSigs ctxt sigs
  binds_w_dus <- mapBagM rnLBind mbinds
  let !(anal_binds, anal_dus) = depAnalBinds binds_w_dus

      valbind'_dus = anal_dus `plusDU` usesOnly sig_fvs

  return (XValBindsLR (NValBinds anal_binds sigs'), valbind'_dus)

rnValBindsRHS _ b = pprPanic "rnValBindsRHS" (ppr b)

---------------------

rnBindLHS :: NameMaker -> SDoc -> CsBind Ps -> RnM (CsBindLR Rn Ps) 
rnBindLHS name_maker _ bind@(FunBind { fun_id = rdr_name, fun_ext = ext }) = do
  name <- applyNameMaker name_maker rdr_name
  return (bind { fun_id = name, fun_ext = ext })
rnBindLHS _ _ b = pprPanic "rnBindLHS" (ppr b)

rnLBind :: LCsBindLR Rn Ps -> RnM (LCsBind Rn, Name, Uses)
rnLBind (L loc bind) = setSrcSpanA loc $ do
  (bind', bndr, dus) <- rnBind 
  return (L loc bind', bndr, dus)

rnBind :: CsBindLR Rn Ps -> RnM (CsBind Rn, Name, Uses)
rnBind bind@(FunBind { fun_id = name, fun_matches = matches }) = do
  let plain_name = unLoc name

  (matches', rhs_fvs) <- rnMatchGroup (mkPrefixFunRhs name) rnLExpr matches

  let is_infix = isInfixFunBind bind
  when is_infix $ checkPrecMatch plain_name matches'

  mod <- getModule
  let fvs' = filterNameSet (nameIsLocalOrFrom mod) rhs_fvs

  fvs' `seq`
    return (bind { fun_matches = matches', fun_ext = fvs' }, plain_name, rhs_fvs)

rnBind other = pprPanic "rnBind" (ppr other)

{- *********************************************************************
*                                                                      *
          Dependency analysis and other support functions
*                                                                      *
********************************************************************* -}

depAnalBinds :: Bag (LCsBind Rn, Name, Uses) -> ([(RecFlag, LCsBinds Rn)], DefUses)
depAnalBinds binds_w_dus = (map get_binds sccs, toOL $ map get_du sccs)
  where
    sccs = depAnal (\(_, defs, _) -> defs)
                   (\(_, _, uses) -> nonDetEltsUniqSet uses)
                   (bagToList binds_w_dus)

    get_binds (AcyclicSCC (bind, _, _)) = (NonRecursive, unitBag bind)
    get_binds (CyclicSCC binds'_w_dus) = (Recursive, listToBag [ b | (b, _, _) <- binds'_w_dus ])

    get_du (AcyclicSCC (_, bndrs, uses)) = (Just (mkNameSet bndrs), uses)
    get_du (CyclicSCC binds'_w_dus) = (Just defs, uses)
      where
        defs = mkNameSet [ b | (_, bs, _) <- binds'_w_dus, b <- bs ]
        uses = unionNameSets [ u | (_, _, u) <- binds'_w_dus ]

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
              Signatures
*                                                                      *
********************************************************************* -}

renameSigs :: CsSigCtxt -> [LSig Ps] -> RnM ([LSig Rn], FreeVars)
renameSigs ctxt sigs = do
  mapM_ dupSigDeclErr (findDupSigs sigs)

  (sigs', sig_fvs) <- mapFvRn (wrapLocFstMA (renameSig ctxt)) sigs

  let (good_sigs, bad_sigs) = partition (okCsSig ctxt) sigs'
  mapM_ misplacedSigErr bad_sigs

  return (good_sigs, sig_fvs)

renameSig :: CsSigCtxt -> Sig Ps -> RnM (Sig Rn, FreeVars)
renameSig ctxt sig@(TypeSig _ v ty) = do
  new_v <- lookupSigOccRnN ctxt sig v
  let doc = TypeSigCtx (ppr_sig_bndr v)
  (new_ty, fvs) <- rnCsSigType doc ty

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
