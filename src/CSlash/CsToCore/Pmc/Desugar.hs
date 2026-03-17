{-# LANGUAGE LambdaCase #-}

module CSlash.CsToCore.Pmc.Desugar where

import CSlash.CsToCore.Pmc.Types
import CSlash.CsToCore.Pmc.Utils
import CSlash.Core (Expr(Var,App))
import CSlash.Data.FastString (unpackFS, lengthFS)
import CSlash.Driver.DynFlags
import CSlash.Cs
-- import CSlash.Tc.Utils.TcMType (shortCutLit)
import CSlash.Types.Var.Id
import CSlash.Types.Var.Class
import CSlash.Core.ConLike
import CSlash.Types.Name
import CSlash.Builtin.Types
-- import CSlash.Builtin.Names (rationalTyConName, toListName)
import CSlash.Types.SrcLoc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Core.DataCon
-- import CSlash.Types.Var (EvVar)
-- import CSlash.Core.Coercion
import CSlash.Tc.Types.Evidence (CsWrapper(..), isIdCsWrapper)
import {-# SOURCE #-} CSlash.CsToCore.Expr (dsExpr, dsLExpr{-, dsSyntaxExpr-})
import {-# SOURCE #-} CSlash.CsToCore.Binds (dsCsWrapper)
import CSlash.CsToCore.Utils (isTrueLCsExpr, selectMatchVar)
-- import CSlash.CsToCore.Match.Literal (dsLit, dsOverLit)
import CSlash.CsToCore.Monad
import CSlash.Core.Type.Rep
import CSlash.Core.Type.Compare( eqType )
import CSlash.Core.Type
import CSlash.Data.Maybe
import CSlash.Types.SourceText (FractionalLit(..))
import Control.Monad (zipWithM, replicateM, mapAndUnzipM)
import Data.List (elemIndex)
import Data.List.NonEmpty ( NonEmpty(..) )
import qualified Data.List.NonEmpty as NE

mkPmLetVar :: Id Zk -> Id Zk -> GrdDag
mkPmLetVar x y = sequencePmGrds [ PmLet x (Var y) | x /= y ]

vanillaConGrd :: Id Zk -> DataCon Zk -> [a] -> PmGrd
vanillaConGrd = panic "vanillaConGrd"

desugarPat :: Id Zk -> Pat Zk -> DsM GrdDag
desugarPat x pat = case pat of
  WildPat _ -> pure GdEnd
  VarPat _ y -> pure (mkPmLetVar (unLoc y) x)
  ParPat _ p -> desugarLPat x p
  AsPat _ (L _ y) p -> (mkPmLetVar y x `gdSeq`) <$> desugarLPat y p
  SigPat _ p _ -> desugarLPat x p
  KdSigPat {} -> panic "desugarPat KdSigPat"
  ImpPat _ _ -> panic "desugarPat ImpPat"
  ConPat {} -> panic "desugarPat ConPat"
  NPat {} -> panic "desugarPat NPat"
  LitPat _ lit -> panic "desugarPat LitPat"
  TuplePat _ pats -> do
    (vars, grdss) <- mapAndUnzipM desugarLPatV pats
    let tuple_con = tupleDataCon (length vars)
    pure $ vanillaConGrd x tuple_con vars `consGrdDag` sequenceGrdDags grdss
  SumPat _ p alt arity -> do
    (y, grds) <- desugarLPatV p
    let sum_con = sumDataCon alt arity
    pure $ vanillaConGrd x sum_con [y] `consGrdDag` grds
  XPat ext -> case ext of
    ExpansionPat orig expansion -> do
      case orig of
        -- Todo: ListPat
        _ -> desugarPat x expansion
    CoPat wrapper p _
      | isIdCsWrapper wrapper -> desugarPat x p
      | WpCast co <- wrapper, panic "isReflexiveTyCo co" -> desugarPat x p
      | otherwise -> do
          (y, grds) <- desugarPatV p
          dsCsWrapper wrapper $ \wrap_rhs_y ->
            pure (PmLet y (wrap_rhs_y (Var x)) `consGrdDag` grds)
    TyPat {} -> pure GdEnd
  TyVarPat {} -> panic "desugarPat TyVarPat"

desugarPatV :: Pat Zk -> DsM (Id Zk, GrdDag)
desugarPatV pat = do
  x <- selectMatchVar pat
  grds <- desugarPat x pat
  pure (x, grds)

desugarLPat :: Id Zk -> LPat Zk -> DsM GrdDag
desugarLPat x = desugarPat x . unLoc

desugarLPatV :: LPat Zk -> DsM (Id Zk, GrdDag)
desugarLPatV = desugarPatV . unLoc

desugarMatches :: [Id Zk] -> NonEmpty (LMatch Zk (LCsExpr Zk)) -> DsM (PmMatchGroup Pre)
desugarMatches vars matches = PmMatchGroup <$> traverse (desugarMatch vars) matches

desugarMatch :: [Id Zk] -> LMatch Zk (LCsExpr Zk) -> DsM (PmMatch Pre)
desugarMatch vars (L match_loc (Match { m_pats = L _ pats, m_grhss = grhss })) = do
  dflags <- getDynFlags
  pats' <- sequenceGrdDags <$> zipWithM desugarLPat vars pats
  grhss' <- desugarGRHSs (locA match_loc) (sep (map ppr pats)) grhss
  return PmMatch { pm_pats = pats', pm_grhss = grhss' }

desugarGRHSs :: SrcSpan -> SDoc -> GRHSs Zk (LCsExpr Zk) -> DsM (PmGRHSs Pre)
desugarGRHSs match_loc pp_pats grhss = do
  grhss' <- traverse (desugarLGRHS match_loc pp_pats)
            .expectJust "desugarGRHSs"
            . NE.nonEmpty
            $ (grhssGRHSs grhss)
  return PmGRHSs{ pgs_grhss = grhss' }

desugarLGRHS :: SrcSpan -> SDoc -> LGRHS Zk (LCsExpr Zk) -> DsM (PmGRHS Pre)
desugarLGRHS match_loc pp_pats (L _ (GRHS _ gs _)) = do
  let rhs_info = case gs of
                   [] -> L match_loc pp_pats
                   (L grd_loc _):_ -> L (locA grd_loc) (pp_pats <+> vbar <+> interpp'SP gs)
  grdss <- traverse (desugarGuard . unLoc) gs
  pure PmGRHS { pg_grds = sequenceGrdDags grdss, pg_rhs = SrcInfo rhs_info }

desugarGuard :: GuardStmt Zk -> DsM GrdDag
desugarGuard guard = case guard of
  BodyStmt _ e -> desugarBoolGuard e
  LetStmt _ binds -> desugarLocalBinds binds
  BindStmt _ p e -> desugarBind p e

sequenceGrdDagMapM :: Applicative f => (a -> f GrdDag) -> [a] -> f GrdDag
sequenceGrdDagMapM f as = sequenceGrdDags <$> traverse f as

desugarLocalBinds :: CsLocalBinds Zk -> DsM GrdDag
desugarLocalBinds (CsValBinds _ (XValBindsLR (NValBinds binds _))) =
  sequenceGrdDagMapM (sequenceGrdDagMapM go) (map snd binds)
  where
    go :: LCsBind Zk -> DsM GrdDag
    go (L _ FunBind{ fun_id = L _ x, fun_body = rhs }) = do
      core_rhs <- dsLExpr rhs
      return $ GdOne (PmLet x core_rhs)
    go (L _ (XCsBindsLR (AbsBinds { abs_kvs = [], abs_tvs = []
                                  , abs_exports = exports, abs_binds = binds }))) = do
      let go_export :: ABExport Zk -> Maybe PmGrd
          go_export ABE{ abe_poly = x, abe_mono = y, abe_wrap = wrap }
            | isIdCsWrapper wrap
            = assertPpr (varType x `eqType` varType y)
              (ppr x $$ ppr (varType x) $$ ppr y $$ ppr (varType y)) $
              Just $ PmLet x (Var y)
            | otherwise
            = Nothing
      let exps = mapMaybe go_export exports
      bs <- sequenceGrdDagMapM go binds
      return (sequencePmGrds exps `gdSeq` bs)
    go _ = return GdEnd
desugarLocalBinds _ = return GdEnd

desugarBind :: LPat Zk -> LCsExpr Zk -> DsM GrdDag
desugarBind p e = dsLExpr e >>= \case
  Var y
    | Nothing <- isDataConId_maybe y
      -> desugarLPat y p
  rhs -> do
    (x, grds) <- desugarLPatV p
    pure (PmLet x rhs `consGrdDag` grds)

desugarBoolGuard :: LCsExpr Zk -> DsM GrdDag
desugarBoolGuard e
  | isJust (isTrueLCsExpr e) = return GdEnd
  | otherwise = dsLExpr e >>= \case
      Var y
        | Nothing <- isDataConId_maybe y
          -> pure (GdOne (vanillaConGrd y trueDataCon [panic "kv and tv args?"]))
      rhs -> do
        x <- mkPmId (panic "boolTy kv and tv args?")
        pure $ sequencePmGrds [PmLet x rhs, vanillaConGrd x trueDataCon [panic "args?"] ]
