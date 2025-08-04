module CSlash.Tc.Gen.Expr where

import CSlash.Cs
-- import CSlash.Cs.Syn.Type
import CSlash.Rename.Utils
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Utils.Unify
import CSlash.Tc.Types.BasicTypes
import CSlash.Types.Basic
import CSlash.Types.Error
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.Map
import CSlash.Types.Unique.Set
import CSlash.Core.Kind
import CSlash.Core.UsageEnv
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Instantiate
import CSlash.Tc.Gen.App
import CSlash.Tc.Gen.Head
-- import CSlash.Tc.Gen.Bind        ( tcLocalBinds )
import CSlash.Rename.Env         ( addUsedGRE )
import CSlash.Tc.Utils.Env
-- import CSlash.Tc.Gen.Arrow
import CSlash.Tc.Gen.Match ( tcBody, tcLambdaMatches{-, tcCaseMatches-}
                           , tcGRHSList )
import CSlash.Tc.Gen.CsType
import CSlash.Tc.Utils.TcMType
import CSlash.Tc.Zonk.TcType
import CSlash.Tc.Types.Origin
import CSlash.Tc.Utils.TcType as TcType
import CSlash.Types.Id
import CSlash.Types.Id.Info
import CSlash.Core.ConLike
import CSlash.Core.DataCon
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set
import CSlash.Types.Name.Reader
import CSlash.Core.TyCon
import CSlash.Core.Type
import CSlash.Tc.Types.Evidence
import CSlash.Builtin.Types
import CSlash.Builtin.Names
-- import CSlash.Builtin.Uniques ( mkBuiltinUnique )
import CSlash.Driver.DynFlags
import CSlash.Types.SrcLoc
import CSlash.Utils.Misc
import CSlash.Data.List.SetOps
import CSlash.Data.Maybe
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic

import Control.Monad
import qualified Data.List.NonEmpty as NE


{- *********************************************************************
*                                                                      *
            Main wrappers
*                                                                      *
********************************************************************* -}

tcPolyLExpr :: LCsExpr Rn -> ExpSigmaType -> TcM (LCsExpr Tc)
tcPolyLExpr (L loc expr) res_ty =
  setSrcSpanA loc
  $ addExprCtxt expr
  $ do expr' <- tcPolyExpr expr res_ty
       return (L loc expr')

tcPolyExpr :: CsExpr Rn -> ExpSigmaType -> TcM (CsExpr Tc) 
tcPolyExpr e (Infer _) = panic "tcPolyExpr infer"
tcPolyExpr e (Check ty) = tcPolyExprCheck e (Left ty)

tcPolyExprCheck :: CsExpr Rn -> Either AnySigmaType TcCompleteSig -> TcM (CsExpr Tc)
tcPolyExprCheck  expr res_ty = outer_skolemize res_ty $ \pat_tys rho_ty ->
  let tc_body (CsPar x (L loc e))
        = setSrcSpanA loc $ do e' <- tc_body e
                               return (CsPar x (L loc e'))

      tc_body e@(CsLam x matches) = do
        (wrap, matches') <- tcLambdaMatches e matches pat_tys (mkCheckExpType rho_ty)
        return (mkCsWrap wrap $ CsLam x matches')

      tc_body e = tcExpr e (mkCheckExpType rho_ty)
  in tc_body expr
  where
    outer_skolemize
      :: Either AnySigmaType TcCompleteSig
      -> ([ExpPatType] -> AnyRhoType -> TcM (CsExpr Tc))
      -> TcM (CsExpr Tc)
    outer_skolemize (Left ty) thing_inside = do
      (wrap, expr') <- tcSkolemizeExpectedType ty thing_inside
      return (mkCsWrap wrap expr')
    outer_skolemize (Right sig) thing_inside = do
      (wrap, expr') <- tcSkolemizeCompleteSig sig thing_inside
      return ( mkCsWrap wrap expr')
        
{- *********************************************************************
*                                                                      *
        tcExpr: the main expression typechecker
*                                                                      *
********************************************************************* -}

tcInferRhoNC :: LCsExpr Rn -> TcM (LCsExpr Tc, AnyRhoType)
tcInferRhoNC = panic "tcInferRhoNC"

tcCheckMonoExpr :: LCsExpr Rn -> AnyRhoType -> TcM (LCsExpr Tc)
tcCheckMonoExpr = panic "tcCheckMonoExpr"

tcExpr :: CsExpr Rn -> ExpRhoType -> TcM (CsExpr Tc)
-- Onto QuickLook
tcExpr e@(CsVar {}) res_ty = tcApp e res_ty
tcExpr e@(CsApp {}) res_ty = tcApp e res_ty
tcExpr e@(OpApp {}) res_ty = tcApp e res_ty
tcExpr e@(ExprWithTySig {}) res_ty = tcApp e res_ty
-- rest
tcExpr e@(CsOverLit _ lit) res_ty = panic "tcExpr CsOverLit"

tcExpr e@(CsLit x lit) res_ty = panic "tcExpr CsLit"

tcExpr (CsUnboundVar _ occ) res_ty = panic "tcExpr CsUnboundVar"

tcExpr (CsPar x expr) res_ty = panic "tcExpr CsPar"

tcExpr (NegApp x expr neg_expr) res_ty = panic "tcExpr NegApp"

tcExpr e@(CsLam x matches) res_ty = panic "tcExpr CsLam"

tcExpr e res_ty = panic "tcExpr other"
