{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE NamedFieldPuns #-}

module CSlash.Rename.Bind where

import {-# SOURCE #-} CSlash.Rename.Expr ( rnExpr, rnLExpr, rnStmts )

import CSlash.Cs
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad
import CSlash.Rename.CsType
import CSlash.Rename.CsKind
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

{- *****************************************************
*                                                      *
                HsLocalBinds
*                                                      *
***************************************************** -}

rnLocalBindsAndThen
  :: CsLocalBinds Ps
  -> (CsLocalBinds Rn -> FreeVars -> RnM (result, FreeVars))
  -> RnM (result, FreeVars)
rnLocalBindsAndThen (EmptyLocalBinds x) thing_inside
  = thing_inside (EmptyLocalBinds x) emptyNameSet
  
rnLocalBindsAndThen (CsValBinds x val_binds) thing_inside 
  = rnLocalValBindsAndThen val_binds $ \val_binds' ->
      thing_inside (CsValBinds x val_binds')

{- *********************************************************************
*                                                                      *
                ValBinds
*                                                                      *
********************************************************************* -}

rnLocalValBindsLHS :: MiniFixityEnv -> CsValBinds Ps -> RnM ([Name], CsValBindsLR Rn Ps)
rnLocalValBindsLHS fix_env binds = do
  binds' <- rnValBindsLHS (localRecNameMaker fix_env) binds

  let bound_names = collectCsValBinders CollNoDictBinders binds'
  envs <- getRdrEnvs
  checkDupAndShadowedNames envs bound_names

  return (bound_names, binds')

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

rnLocalValBindsRHS :: NameSet -> CsValBindsLR Rn Ps -> RnM (CsValBinds Rn, DefUses)
rnLocalValBindsRHS bound_names binds = rnValBindsRHS (LocalBindCtxt bound_names) binds

rnLocalValBindsAndThen
  :: CsValBinds Ps
  -> (CsValBinds Rn -> FreeVars -> RnM (result, FreeVars))
  -> RnM (result, FreeVars)
rnLocalValBindsAndThen binds@(ValBinds {}) thing_inside = do
  new_fixities <- makeMiniFixityEnv []

  (bound_names, new_lhs) <- rnLocalValBindsLHS new_fixities binds

  bindLocalNamesFV bound_names
    $ addLocalFixities new_fixities bound_names
    $ do (binds', dus) <- rnLocalValBindsRHS (mkNameSet bound_names) new_lhs
         (result, result_fvs) <- thing_inside binds' (allUses dus)

         let real_uses = findUses dus result_fvs
         warnUnusedLocalBinds bound_names real_uses

         let all_uses = allUses dus `plusFV` result_fvs

         return (result, all_uses)

rnLocalValBindsAndThen bs _ = pprPanic "rnLocalValBindsAndThen" (ppr bs)

---------------------

rnBindLHS :: NameMaker -> SDoc -> CsBind Ps -> RnM (CsBindLR Rn Ps) 
rnBindLHS name_maker _ bind@(FunBind { fun_id = rdr_name, fun_ext = ext }) = do
  name <- applyNameMaker name_maker rdr_name
  return (bind { fun_id = name, fun_ext = ext })
rnBindLHS _ _ b = pprPanic "rnBindLHS" (ppr b)

rnLBind :: LCsBindLR Rn Ps -> RnM (LCsBind Rn, Name, Uses)
rnLBind (L loc bind) = setSrcSpanA loc $ do
  (bind', bndr, dus) <- rnBind bind
  return (L loc bind', bndr, dus)

rnBind :: CsBindLR Rn Ps -> RnM (CsBind Rn, Name, Uses)
rnBind bind@(FunBind { fun_id = name, fun_body = body }) = do
  let plain_name = unLoc name

  -- (matches', rhs_fvs) <- rnMatchGroup (mkPrefixFunRhs name) rnLExpr matches
  (body', rhs_fvs) <- rnLExpr body

  mod <- getModule
  let fvs' = filterNameSet (nameIsLocalOrFrom mod) rhs_fvs

  fvs' `seq`
    return (bind { fun_body = body', fun_ext = fvs' }, plain_name, rhs_fvs)

rnBind other = pprPanic "rnBind" (ppr other)

{- *********************************************************************
*                                                                      *
          Dependency analysis and other support functions
*                                                                      *
********************************************************************* -}

depAnalBinds :: Bag (LCsBind Rn, Name, Uses) -> ([(RecFlag, LCsBinds Rn)], DefUses)
depAnalBinds binds_w_dus = (map get_binds sccs, toOL $ map get_du sccs)
  where
    sccs = depAnal (\(_, def, _) -> [def])
                   (\(_, _, uses) -> nonDetEltsUniqSet uses)
                   (bagToList binds_w_dus)

    get_binds (AcyclicSCC (bind, _, _)) = (NonRecursive, unitBag bind)
    get_binds (CyclicSCC binds'_w_dus) = (Recursive, listToBag [ b | (b, _, _) <- binds'_w_dus ])

    get_du (AcyclicSCC (_, bndr, uses)) = (Just (mkNameSet [bndr]), uses)
    get_du (CyclicSCC binds'_w_dus) = (Just defs, uses)
      where
        defs = mkNameSet [ b | (_, b, _) <- binds'_w_dus ]
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
  return (TypeSig noAnn new_v new_ty, fvs)
renameSig ctxt (FixSig _ fsig) = do
  new_fsig <- rnSrcFixityDecl ctxt fsig
  return (FixSig noAnn new_fsig, emptyFVs)
renameSig _ other = pprPanic "renameSig" (ppr other)

ppr_sig_bndr :: LocatedN RdrName -> SDoc
ppr_sig_bndr b = quotes (ppr b)

okCsSig :: CsSigCtxt -> LSig (CsPass p) -> Bool
okCsSig _ _ = True      

-------------------
findDupSigs :: [LSig Ps] -> [NonEmpty (LocatedN RdrName, Sig Ps)]
findDupSigs sigs = findDupsEq matching_sig (concatMap (expand_sig . unLoc) sigs)
  where
    expand_sig :: Sig Ps -> [(LocatedN RdrName, Sig Ps)]
    expand_sig sig@(FixSig _ (FixitySig _ n _)) = [(n, sig)]
    expand_sig sig@(TypeSig _ n _) = [(n, sig)]
    expand_sig _ = panic "expand_sig/unreachable"

    matching_sig :: (LocatedN RdrName, Sig Ps) -> (LocatedN RdrName, Sig Ps) -> Bool
    matching_sig (L _ n1, sig1) (L _ n2, sig2) = n1 == n2 && mtch sig1 sig2

    mtch (FixSig {}) (FixSig {}) = True
    mtch (TypeSig {}) (TypeSig {}) = True
    mtch _ _ = False

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
  => BindKVs
  -> CsMatchContextRn
  -> (LocatedA (body Ps) -> RnM (LocatedA (body Rn), FreeVars))
  -> MatchGroup Ps (LocatedA (body Ps))
  -> RnM (MatchGroup Rn (LocatedA (body Rn)), FreeVars)
rnMatchGroup bindkvs ctxt rnBody (MG { mg_alts = L lm ms, mg_ext = origin }) = do
  when (null ms) $ panic "addErr (TcRnEmptyCase ctxt)"
  (new_ms, ms_fvs) <- mapFvRn (rnMatch bindkvs ctxt rnBody) ms
  return (mkMatchGroup origin (L lm new_ms), ms_fvs)

rnMatch
  :: RnMatchAnnoBody body
  => BindKVs
  -> CsMatchContextRn
  -> (LocatedA (body Ps) -> RnM (LocatedA (body Rn), FreeVars))
  -> LMatch Ps (LocatedA (body Ps))
  -> RnM (LMatch Rn (LocatedA (body Rn)), FreeVars)
rnMatch bindkvs ctxt rnBody = wrapLocFstMA (rnMatch' bindkvs ctxt rnBody)

rnMatch'
  :: RnMatchAnnoBody body
  => BindKVs
  -> CsMatchContextRn
  -> (LocatedA (body Ps) -> RnM (LocatedA (body Rn), FreeVars))
  -> Match Ps (LocatedA (body Ps))
  -> RnM (Match Rn (LocatedA (body Rn)), FreeVars)
rnMatch' bindkvs ctxt rnBody (Match { m_pats = L l pats, m_grhss = grhss })
 = rnPats bindkvs ctxt pats $ \pats' -> do
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

{- *********************************************************************
*                                                                      *
              Error messages
*                                                                      *
********************************************************************* -}

dupSigDeclErr :: NonEmpty (LocatedN RdrName, Sig Ps) -> RnM ()
dupSigDeclErr pairs@((L loc _, _) :| _) = addErrAt (locA loc) $ panic "TcRnDuplicateSigDecl pairs"

misplacedSigErr :: LSig Rn -> RnM ()
misplacedSigErr (L loc sig) = addErrAt (locA loc) $ panic "TcRnMisplacedSigDecl sig"
