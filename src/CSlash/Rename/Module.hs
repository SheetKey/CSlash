{-# LANGUAGE FlexibleContexts #-}

module CSlash.Rename.Module where

import Prelude hiding ( head )

-- import {-# SOURCE #-} GHC.Rename.Expr( rnLExpr )
-- import {-# SOURCE #-} GHC.Rename.Splice ( rnSpliceDecl, rnTopSpliceDecls )

import CSlash.Cs
-- import GHC.Types.FieldLabel
import CSlash.Types.Name.Reader
-- import GHC.Rename.HsType
import CSlash.Rename.Bind
-- import GHC.Rename.Doc
import CSlash.Rename.Env
-- import GHC.Rename.Utils ( mapFvRn, bindLocalNames
--                         , checkDupRdrNames, bindLocalNamesFV
--                         , checkShadowedRdrNames, warnUnusedTypePatterns
--                         , newLocalBndrsRn
--                         , noNestedForallsContextsErr
--                         , addNoNestedForallsContextsErr, checkInferredVars )
-- import GHC.Rename.Unbound ( mkUnboundName, notInScopeErr, WhereLooking(WL_Global) )
import CSlash.Rename.Names
import CSlash.Tc.Errors.Types
-- import GHC.Tc.Gen.Annotation ( annCtxt )
import CSlash.Tc.Utils.Monad
-- import CSlash.Tc.Types.Origin ( TypedThing(..) )

-- import GHC.Types.ForeignCall ( CCallTarget(..) )
import CSlash.Unit
import CSlash.Unit.Module.Warnings
-- import CSlash.Builtin.Names( applicativeClassName, pureAName, thenAName
--                            , monadClassName, returnMName, thenMName
--                            , semigroupClassName, sappendName
--                            , monoidClassName, mappendName
--                            )
import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.Name.Env
import CSlash.Utils.Outputable
import CSlash.Data.Bag
import CSlash.Types.Basic  ( TypeOrKind(..) )
import CSlash.Data.FastString
import CSlash.Types.SrcLoc as SrcLoc
import CSlash.Driver.DynFlags
import CSlash.Utils.Misc   ( lengthExceeds, partitionWith )
import CSlash.Utils.Panic
import CSlash.Driver.Env ( CsEnv(..), cs_home_unit)
import CSlash.Data.List.SetOps ( findDupsEq, removeDupsOn, equivClasses )
import CSlash.Data.Graph.Directed ( SCC, flattenSCC, flattenSCCs, Node(..)
                               , stronglyConnCompFromEdgedVerticesUniq )
import CSlash.Types.Unique.Set
import CSlash.Data.OrdList
-- import qualified GHC.LanguageExtensions as LangExt
-- import GHC.Core.DataCon ( isSrcStrict )

import Control.Monad
import Control.Arrow ( first )
import Data.Foldable ( toList, for_ )
import Data.List ( mapAccumL )
import Data.List.NonEmpty ( NonEmpty(..), head, nonEmpty )
import Data.Maybe ( isNothing, fromMaybe, mapMaybe )
import qualified Data.Set as Set ( difference, fromList, toList, null )
import CSlash.Types.GREInfo (ConInfo, mkConInfo{-, conInfoFields-})

rnSrcDecls :: CsGroup Ps -> RnM (TcGblEnv, CsGroup Rn)
rnSrcDecls group@(CsGroup { cs_valds = val_decls
                          , cs_typeds = type_decls
                          , cs_fixds = fix_decls
                          }) = do
  local_fix_env <- makeMiniFixityEnv $ csGroupTopLevelFixitySigs group

  (tc_envs, tc_bndrs) <- getLocalNonValBinders local_fix_env group

  restoreEnvs tc_envs $ do
    failIfErrsM

    new_lhs <- rnTopBindsLHS local_fix_env val_decls
    let id_bndrs = collectCsIdBinders CollNoDictBinders new_lhs
    traceRn "rnSrcDecls" (ppr id_bndrs)
    tc_envs <- extendGlobalRdrEnvRn (map (mkLocalVanillaGRE NoParent) id_bndrs) local_fix_env
    restoreEnvs tc_envs $ do
      traceRn "Start rnTypeDecls" (ppr type_decls)
      (rn_type_decls, src_fvs1) <- rnTypeDecls type_decls

      traceRn "Start rnmono" empty
      let val_bndr_set = mkNameSet id_bndrs
      (rn_val_decls, bind_dus) <- rnValBindsRHS (TopSigCtxt val_bndr_set) new_lhs
      traceRn "finish rnmono" (ppr rn_val_decls)

      let all_bndrs = tc_bndrs `unionNameSet` val_bndr_set
      traceRn "rnSrcDecls fixity" $
        vcat [ text "all_bndrs:" <+> ppr all_bndrs ]
      rn_fix_decls <- mapM (mapM (rnSrcFixityDecl (TopSigCtxt all_bndrs))) fix_decls
  
      last_tcg_env <- getGblEnv
      let rn_group = CsGroup { cs_ext = noExtField
                             , cs_valds = rn_val_decls
                             , cs_typeds = rn_type_decls
                             , cs_fixds = rn_fix_decls
                             }
          tcf_bndrs = csTyForeignBinders rn_type_decls
          other_defs = (Just (mkNameSet tcf_bndrs), emptyNameSet)
          other_fvs = src_fvs1

          src_dus = unitOL other_defs `plusDU` bind_dus `plusDU` usesOnly other_fvs

          final_tcg_env = last_tcg_env `addTcgDUs` src_dus

      traceRn "finish rnSrc" (ppr rn_group)
      traceRn "finish Dus" (ppr src_dus)
      return (final_tcg_env, rn_group)

addTcgDUs :: TcGblEnv -> DefUses -> TcGblEnv
addTcgDUs tcg_env dus = tcg_env { tcg_dus = tcg_dus tcg_env `plusDU` dus }

{- **************************************************************
         *                                                      *
      Renaming type declarations
*                                                               *
************************************************************** -}

rnTypeDecls :: [TypeGroup Ps] -> RnM ([TypeGroup Rn], FreeVars)
rnTypeDecls type_ds = do
  panic "rnTypeDecls"

{- *****************************************************
*                                                      *
        mkGroup
*                                                      *
***************************************************** -}

mkGroup :: [LCsDecl Ps] -> CsGroup Ps
mkGroup = addl emptyRdrGroup

addl :: CsGroup Ps -> [LCsDecl Ps] -> CsGroup Ps
addl gp [] = gp
addl gp (L l d : ds) = add gp l d ds

add :: CsGroup Ps -> SrcSpanAnnA -> CsDecl Ps -> [LCsDecl Ps] -> CsGroup Ps
add gp@(CsGroup { cs_fixds = ts }) l (SigD _ (FixSig _ f)) ds
  = addl (gp { cs_fixds = L l f : ts }) ds

add gp@(CsGroup { cs_typeds = ts }) l (SigD _ s@(KindSig _ _ _)) ds
  = addl (gp { cs_typeds = add_kisig (L l s) ts }) ds

add gp@(CsGroup { cs_valds = ts }) l (SigD _ d) ds
  = addl (gp { cs_valds = add_sig (L l d) ts }) ds

add gp@(CsGroup { cs_typeds = ts }) l (ValD _ d@(TyFunBind{})) ds
  = addl (gp { cs_typeds = add_typed (L l d) ts }) ds

add gp@(CsGroup { cs_valds = ts }) l (ValD _ d) ds
  = addl (gp { cs_valds = add_bind (L l d) ts }) ds

add_typed
  :: OutputableBndrId p => LCsBind (CsPass p) -> [TypeGroup (CsPass p)] -> [TypeGroup (CsPass p)]
add_typed d@(L _ TyFunBind{}) [] = [TypeGroup { group_ext = noExtField
                                          , group_typeds = [d]
                                          , group_kisigs = []
                                          }
                               ]
add_typed d@(L _ TyFunBind{}) (ds@(TypeGroup { group_typeds = typeds }) : dss)
  = ds { group_typeds = d : typeds } : dss
add_typed (L _ d) _ = pprPanic "add_typed" (ppr d)

add_kisig
  :: OutputableBndrId p => LSig (CsPass p) -> [TypeGroup (CsPass p)] -> [TypeGroup (CsPass p)]
add_kisig d@(L _ KindSig{}) [] = [TypeGroup { group_ext = noExtField
                                        , group_typeds = []
                                        , group_kisigs = [d]
                                        }
                             ]
add_kisig d@(L _ KindSig{}) (ds@(TypeGroup { group_kisigs = kisigs }) : dss)
  = ds { group_kisigs = d : kisigs } : dss
add_kisig d _ = pprPanic "add_kisig" (ppr d)

add_bind
  :: OutputableBndrId p => LCsBind (CsPass p) -> CsValBinds (CsPass p) -> CsValBinds (CsPass p)
add_bind b@(L _ (TyFunBind{})) _ = pprPanic "add_bind" (ppr b)
add_bind b (ValBinds x bs sigs) = ValBinds x (bs `snocBag` b) sigs
add_bind _ (XValBindsLR{}) = panic "add_bind"

add_sig :: OutputableBndrId p => LSig (CsPass p) -> CsValBinds (CsPass p) -> CsValBinds (CsPass p)
add_sig k@(L _ (KindSig{})) _ = pprPanic "add_sig" (ppr k)
add_sig s (ValBinds x bs sigs) = ValBinds x bs (s : sigs)
add_sig _ (XValBindsLR{}) = panic "add_sig"
