module CSlash.CsToCore.Expr where

-- import GHC.HsToCore.Match
-- import GHC.HsToCore.Match.Literal
import CSlash.CsToCore.Binds
-- import GHC.HsToCore.GuardedRHSs
-- import GHC.HsToCore.ListComp
-- import GHC.HsToCore.Utils
-- import GHC.HsToCore.Arrows
import CSlash.CsToCore.Monad
-- import GHC.HsToCore.Pmc
-- import GHC.HsToCore.Errors.Types
import CSlash.Types.SourceText
import CSlash.Types.Name hiding (varName)
-- import GHC.HsToCore.Quote
-- import GHC.HsToCore.Ticks (stripTicksTopHsExpr)
import CSlash.Cs

import CSlash.Tc.Utils.TcType
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Utils.Monad
import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Core.Type.Rep
import CSlash.Core
import CSlash.Core.Utils
import CSlash.Core.Make

import CSlash.Driver.Session
-- import GHC.Types.CostCentre
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.Var.Id.Make
import CSlash.Unit.Module
import CSlash.Core.ConLike
import CSlash.Core.DataCon
import CSlash.Builtin.Types
import CSlash.Builtin.Names
import CSlash.Types.Basic hiding (ConLike)
import CSlash.Types.SrcLoc
import CSlash.Types.Tickish
import CSlash.Utils.Misc
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic
-- import GHC.Core.PatSyn
import Control.Monad
import CSlash.Types.Error

{- *********************************************************************
*                                                                      *
                dsLocalBinds, dsValBinds
*                                                                      *
********************************************************************* -}

{- *********************************************************************
*                                                                      *
*              Variables, constructors, literals                       *
*                                                                      *
********************************************************************* -}


dsLExpr :: LCsExpr Zk -> DsM CoreExpr
dsLExpr (L loc e) = putSrcSpanDsA loc $ dsExpr e

dsExpr :: CsExpr Zk -> DsM CoreExpr

dsExpr e@(CsVar {}) = dsApp e
dsExpr e@(CsApp {}) = dsApp e

dsExpr (CsPar _ e) = dsLExpr e
dsExpr (ExprWithTySig _ e _) = dsLExpr e

dsExpr (CsLit _ lit) = do panic "lit"

dsExpr (CsOverLit _ lit) = do panic "overlit"
  -- warnAboutOverflowedOverLit lit
  -- dsOverLit lit

dsExpr e@(XExpr ext_expr_tc)
  = case ext_expr_tc of
      WrapExpr {} -> dsApp e
      ConLike {} -> dsApp e
      ExpandedThing (OrigExpr{}) e -> dsExpr e

-- Simpler than GHC because we always have LexicalNegation On      
dsExpr (NegApp _ expr neg_expr) = panic "negapp"

-- dsExpr (CsLam (_, fun_kis) mg) = do
--   (ids, body) <- matchWrapper LamAlt Nothing mg
--   massertPpr (ids `equalLength` fun_kis)
--     $ vcat [ text "dsExpr CsLam fun_kis and id binder length mismatch"
--            , text "fun_kis" <+> ppr fun_kis
--            , text "ids" <+> ppr ids
--            , text "body" <+> ppr body ]
--   return $ mkCoreLams (ids `zip` Just <$> fun_kis) body

dsExpr (CsTyLam {}) = panic "CsTyLam"

dsExpr other = pprPanic "dsExpr" (ppr other)

{- *********************************************************************
*                                                                      *
*              Desugaring applications
*                                                                      *
********************************************************************* -}

dsApp :: CsExpr Zk -> DsM CoreExpr
dsApp e = ds_app e [] []

ds_lapp :: LCsExpr Zk -> [LCsExpr Zk] -> [CoreExpr] -> DsM CoreExpr
ds_lapp (L loc e) cs_args core_args
  = putSrcSpanDsA loc $
    ds_app e cs_args core_args

ds_app :: CsExpr Zk -> [LCsExpr Zk] -> [CoreExpr] -> DsM CoreExpr

ds_app (CsPar _ e) cs_args core_args = ds_lapp e cs_args core_args

ds_app (CsApp _ fun arg) cs_args core_args = do
  core_arg <- dsLExpr arg
  ds_lapp fun (arg : cs_args) (core_arg : core_args)

ds_app (XExpr (WrapExpr cs_wrap fun)) cs_args core_args = do
  (fun_wrap, all_args) <- splitCsWrapperArgs cs_wrap core_args
  if isIdCsWrapper fun_wrap
    then ds_app fun cs_args all_args
    else do core_fun <- dsCsWrapper fun_wrap $ \core_wrap -> do
              core_fun <- dsExpr fun
              return $ core_wrap core_fun
            return $ mkCoreApps core_fun all_args

ds_app (XExpr (ConLike con)) _ core_args = do
  ds_con <- dsCsConLike con
  return $ mkCoreApps ds_con core_args

ds_app (CsVar _ lfun) cs_args core_args = ds_app_var lfun cs_args core_args

ds_app e _ core_args = do
  core_e <- dsExpr e
  return $ mkCoreApps core_e core_args

ds_app_var :: LocatedN (Id Zk) -> [LCsExpr Zk] -> [CoreExpr] -> DsM CoreExpr
ds_app_var (L loc fun_id) cs_args core_args = ds_app_finish fun_id core_args

ds_app_finish :: Id Zk -> [CoreExpr] -> DsM CoreExpr
ds_app_finish fun_id core_args = return $ mkCoreApps (Var fun_id) core_args

splitCsWrapperArgs :: CsWrapper Zk -> [CoreArg] -> DsM (CsWrapper Zk, [CoreArg])
splitCsWrapperArgs wrap args = go wrap args
  where
    go (WpTyApp ty) args = return (WpHole, Type ty : args)
    go (WpKiCoApp kco) args = return (WpHole, KiCo kco : args)
    go (WpKiApp ki) args = return (WpHole, Kind ki : args)
    go (WpCompose w1 w2) args = do
      (w1', args') <- go w1 args
      if isIdCsWrapper w1'
        then go w2 args'
        else return (w1' <.> w2, args')
    go wrap args = return (wrap, args)

dsCsConLike :: ConLike Zk -> DsM CoreExpr
dsCsConLike (RealDataCon dc) = return $ varToCoreExpr $ dataConId dc
dsCsConLike PatSynCon = panic "dsCoConLike PatSynCon"
