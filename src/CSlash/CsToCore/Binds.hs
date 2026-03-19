{-# LANGUAGE TupleSections #-}

module CSlash.CsToCore.Binds where

import CSlash.Driver.DynFlags
import CSlash.Driver.Config
import CSlash.Unit.Module

import {-# SOURCE #-} CSlash.CsToCore.Expr  ( dsLExpr )
-- import {-# SOURCE #-} GHC.HsToCore.Match ( matchWrapper )

-- import GHC.HsToCore.Pmc.Utils( tracePm )

import CSlash.CsToCore.Monad
import CSlash.CsToCore.Errors.Types
-- import GHC.HsToCore.GuardedRHSs
import CSlash.CsToCore.Utils
-- import GHC.HsToCore.Pmc ( addTyCs, pmcGRHSs )

import CSlash.Cs
import CSlash.Core as Core
-- import GHC.Core.SimpleOpt    ( simpleOptExpr )
-- import GHC.Core.Opt.OccurAnal ( occurAnalyseExpr )
import CSlash.Core.Make
-- import GHC.Core.Utils
import CSlash.Core.Opt.Arity     ( etaExpand )
import CSlash.Core.Unfold.Make
-- import GHC.Core.FVs
import CSlash.Core.Predicate
import CSlash.Core.TyCon
import CSlash.Core.Type
import CSlash.Core.Kind
-- import GHC.Core.Coercion
import CSlash.Core.Type.Compare( eqType )

import CSlash.Builtin.Names
-- import CSlash.Builtin.Types ( charTy )

import CSlash.Tc.Types.Evidence

import CSlash.Types.Var.Id
-- import GHC.Types.Id.Make ( nospecId )
import CSlash.Types.Name
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Types.SrcLoc
import CSlash.Types.Basic
import CSlash.Types.Unique.Set( nonDetEltsUniqSet )

import CSlash.Data.Maybe
import CSlash.Data.OrdList
import CSlash.Data.Graph.Directed
import CSlash.Data.Bag
import qualified Data.Set as S

import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.Misc
import CSlash.Utils.Trace
import CSlash.Utils.Monad
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Control.Monad

{-**********************************************************************
*                                                                      *
           Desugaring a MonoBinds
*                                                                      *
**********************************************************************-}

dsTopLCsBinds :: LCsBinds Zk -> DsM (OrdList (Id Zk, CoreExpr))
dsTopLCsBinds binds = do
  prs <- dsLCsBinds binds
  return $ toOL prs

dsLCsBinds :: LCsBinds Zk -> DsM [(Id Zk, CoreExpr)]
dsLCsBinds binds = do
  ds_bs <- mapM dsLCsBind binds
  return $ foldr (++) [] ds_bs

dsLCsBind :: LCsBind Zk -> DsM [(Id Zk, CoreExpr)]
dsLCsBind (L loc bind) = do
  dflags <- getDynFlags
  putSrcSpanDs (locA loc) $ dsCsBind dflags bind

dsCsBind :: DynFlags -> CsBind Zk -> DsM [(Id Zk, CoreExpr)]
dsCsBind dflags b@(FunBind { fun_id = L loc fun
                           , fun_body = body
                           , fun_ext = (co_fn, tick)
                           })
  = dsCsWrapper co_fn $ \core_wrap -> do
      body <- dsLExpr body -- might need to be special like 'tcFunBody' in the TypeChecker
                           -- to handle the case that body is a tylam
      let body' = mkOptTickBox tick body
          rhs = core_wrap body'
          core_binds = makeCorePair dflags fun rhs
      return [core_binds]

dsCsBind dflags (XCsBindsLR (AbsBinds { abs_tvs = tyvars, abs_kvs = kivars
                                      , abs_exports = exports
                                      , abs_binds = binds, abs_sig = has_sig }))
  = assertPpr (null tyvars) (text "dsCsBind/AbsBinds has nonempty tyvars") $
    assertPpr (null kivars) (text "dsCsBind/AbsBinds has nonempty kivars") $ do
      ds_binds <- dsLCsBinds binds
      dsAbsBinds dflags exports ds_binds (isSingleton binds) has_sig

dsCsBind _ bind = pprPanic "dsCsBind" (ppr bind)

dsAbsBinds
  :: DynFlags
  -> [ABExport Zk]
  -> [(Id Zk, CoreExpr)]
  -> Bool
  -> Bool
  -> DsM [(Id Zk, CoreExpr)]
dsAbsBinds dflags exports bind_prs is_singleton has_sig
  | [export] <- exports
  , ABE { abe_poly = global_id
        , abe_mono = local_id
        , abe_wrap = wrap } <- export
  = dsCsWrapper wrap $ \core_wrap -> 
      let rhs = core_wrap body
          body | has_sig
               , [(_, lrhs)] <- bind_prs
               = lrhs
               | otherwise
               = mkLetRec (map (\(id, e) -> (Core.Id id, e)) bind_prs) (Var local_id)
          main_bind = makeCorePair dflags global_id rhs
      in return [main_bind]
  | otherwise
  = do let wrap_first_bind f ((main, main_rhs) : other_binds)
             = ((main, f main_rhs) : other_binds)
           wrap_first_bind _ [] = panic "dsAbsBinds received an empty binding list"

           mk_main :: ABExport Zk -> DsM (Id Zk, CoreExpr)
           mk_main (ABE { abe_poly = gbl_id, abe_mono = lcl_id, abe_wrap = wrap }) = do
             dsCsWrapper wrap $ \core_wrap ->
               return ( gbl_id `setInlinePragma` defaultInlinePragma
                      , core_wrap (Var lcl_id) )

       main_prs <- mapM mk_main exports
       let final_prs = map mk_aux_bind bind_prs
       return (final_prs ++ main_prs)
  -- | otherwise
  -- = do -- let aux_binds = Rec $ map mk_aux_bind bind_prs
  --      -- locals 
  --      panic "dsAbsBinds unfinished"
  where
    mk_aux_bind :: (Id Zk, CoreExpr) -> (Id Zk, CoreExpr)
    mk_aux_bind (lcl_id, rhs) = let lcl_w_inline = lookupVarEnv inline_env lcl_id `orElse` lcl_id
                                in makeCorePair dflags lcl_w_inline rhs

    inline_env :: VarEnv (Id Zk) (Id Zk)
    inline_env = mkVarEnv [ (lcl_id, setInlinePragma lcl_id prag)
                          | ABE { abe_mono = lcl_id, abe_poly = gbl_id } <- exports
                          , let prag = idInlinePragma gbl_id ]

makeCorePair :: DynFlags -> Id Zk -> CoreExpr -> (Id Zk, CoreExpr)
makeCorePair dflags gbl_id rhs
  = case inlinePragmaSpec inline_prag of
      NoUserInlinePrag -> (gbl_id, rhs)
      NoInline {} -> (gbl_id, rhs)
      Opaque {} -> (gbl_id, rhs)
      Inlinable {} -> (gbl_id `setIdUnfolding` inlinable_unf, rhs)
      Inline {} -> inline_pair
  where
    inline_prag = idInlinePragma gbl_id
    simpl_opts = initSimpleOpts dflags
    inlinable_unf = mkInlinableUnfolding simpl_opts StableUserSrc rhs
    inline_pair
      | Just arity <- inlinePragmaSat inline_prag
      = ( gbl_id `setIdUnfolding`
          mkInlineUnfoldingWithArity simpl_opts StableUserSrc arity rhs
        , etaExpand arity rhs )
      | otherwise
      = pprTrace "makeCorePair: arity missing" (ppr gbl_id) $
        panic "(gbl_id `setIdUnfolding` mkInlineUnfoldingNoArity simpl_opts StableUserSrc rhs, rhs)"
                                                

{-**********************************************************************
*                                                                      *
           Desugaring evidence
*                                                                      *
**********************************************************************-}
 
dsCsWrapper :: CsWrapper Zk -> ((CoreExpr -> CoreExpr) -> DsM a) -> DsM a
dsCsWrapper cs_wrap thing_inside
  = ds_cs_wrapper cs_wrap $ \core_wrap ->
    -- TODO: Do I need to add KiCo preds to the PhiCt context??
                              thing_inside core_wrap


ds_cs_wrapper :: CsWrapper Zk -> ((CoreExpr -> CoreExpr) -> DsM a) -> DsM a
ds_cs_wrapper wrap = go wrap
  where
    go WpHole k = k $ \e -> e
    go (WpTyApp ty) k = k $ \e -> App e (Type ty)
    go (WpKiCoApp kco) k = k $ \e -> App e (KiCo kco)
    go (WpKiApp ki) k = k $ \e -> App e (Kind ki)
    go (WpTyLam tv) k = k $ Lam (Tv tv) Nothing
    go (WpKiCoLam kcv) k = k $ Lam (KCv kcv) Nothing
    go (WpKiLam kv) k = k $ Lam (Kv kv) Nothing
    go (WpCast co) k = k $ \e -> mkCastDs e co
    go (WpMultCoercion kco) k = pprPanic "ds_cs_wrapper WpMultCoercion" (ppr kco)
    go (WpCompose c1 c2) k = go c1 $ \w1 ->
                             go c2 $ \w2 ->
                             k (w1 . w2)
    go (WpFun c_res ki_fun ty_arg) k = do
      x <- newSysLocalDs ty_arg
      go c_res $ \w_res ->
        let app f a = mkCoreApp (text "dsCsWrapper") f a
        in k $ \e -> Lam (Core.Id x) (Just ki_fun) (w_res (app e (Var x)))
