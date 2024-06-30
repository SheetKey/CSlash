{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module CSlash.Cs.Expr
  ( module CSlash.Language.Syntax.Expr
  , module CSlash.Cs.Expr
  ) where

import Prelude hiding ((<>))

import CSlash.Language.Syntax.Expr
import CSlash.Language.Syntax.Extension

import CSlash.Data.FastString
import CSlash.Cs.Extension
import CSlash.Cs.Lit
import CSlash.Cs.Pat
import CSlash.Parser.Annotation
import CSlash.Types.Basic
import CSlash.Types.SrcLoc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

type instance Anno (StmtLR Rn Rn (LocatedA (body Rn))) = SrcSpanAnnA

instance (OutputableBndrId p) => Outputable (CsExpr (CsPass p)) where
  ppr expr = pprExpr expr

pprLExpr :: (OutputableBndrId p) => LCsExpr (CsPass p) -> SDoc
pprLExpr (L _ e) = pprExpr e

pprExpr :: (OutputableBndrId p) => CsExpr (CsPass p) -> SDoc
pprExpr e | isAtomicCsExpr e || isQuietCsExpr e = ppr_expr e
          | otherwise = pprDeeper (ppr_expr e)

isQuietCsExpr :: CsExpr id -> Bool
isQuietCsExpr (CsPar {}) = True
isQuietCsExpr (CsApp {}) = True
isQuietCsExpr (OpApp {}) = True
isQuietCsExpr _ = False

ppr_lexpr :: (OutputableBndrId p) => LCsExpr (CsPass p) -> SDoc
ppr_lexpr e = ppr_expr (unLoc e)

ppr_expr
  :: (OutputableBndrId p)
  => CsExpr (CsPass p)
  -> SDoc
ppr_expr (CsVar _ (L _ v)) = pprPrefixOcc v
ppr_expr (CsUnboundVar _ uv) = pprPrefixOcc uv
ppr_expr (CsLit _ lit) = ppr lit
ppr_expr (CsLam _ matches) = pprMatches matches
ppr_expr e@(CsApp {}) = ppr_apps e []
ppr_expr (CsTyLam _ matches) = pprMatches matches
ppr_expr e@(CsTyApp {}) = ppr_tyapps e []
ppr_expr (OpApp _ e1 op e2)
  | Just pp_op <- ppr_infix_expr (unLoc op)
  = pp_infixly pp_op
  | otherwise
  = pp_prefixly
  where
    pp_e1 = pprDebugParendExpr opPrec e1
    pp_e2 = pprDebugParendExpr opPrec e2
    pp_prefixly
      = hang (ppr op) 2 (sep [pp_e1, pp_e2])
    pp_infixly pp_op
      = hang pp_e1 2 (sep [pp_op, nest 2 pp_e2])
ppr_expr (CsPar _ e) = parens (ppr_lexpr e)
ppr_expr (SectionL _ expr op)
  | Just pp_op <- ppr_infix_expr (unLoc op)
  = pp_infixly pp_op
  | otherwise
  = pp_prefixly
  where
    pp_expr = pprDebugParendExpr opPrec expr
    pp_prefixly = hang (hsep [text " \\ x_ ->", ppr op])
                       4 (hsep [pp_expr, text "x, )"])
    pp_infixly v = (sep [pp_expr, v])
ppr_expr (SectionR _ op expr)
  | Just pp_op <- ppr_infix_expr (unLoc op)
  = pp_infixly pp_op
  | otherwise
  = pp_prefixly
  where
    pp_expr = pprDebugParendExpr opPrec expr
    pp_prefixly = hang (hsep [ text "( \\ x_ ->"
                             , ppr op
                             , text "x_"])
                       4 (pp_expr <> rparen)
    pp_infixly v = sep [v, pp_expr]
ppr_expr (ExplicitTuple _ exprs)
  = parens (fcat (ppr_tup_args exprs))
  where
    ppr_tup_args [] = []
    ppr_tup_args (Present _ e : es)
      = (ppr_lexpr e <> punc es) : ppr_tup_args es
    ppr_tup_args (Missing _ : es)
      = punc es : ppr_tup_args es
    punc (Present {} : _) = comma <> space
    punc (Missing {} : _) = comma
    punc [] = empty
ppr_expr (ExplicitSum _ alt arity expr)
  = parens $ ppr_bars (alt - 1)
    <+> ppr expr
    <+> ppr_bars (arity - alt)
  where
    ppr_bars n = hsep (replicate n (char '|'))
ppr_expr (CsCase _ expr matches@(MG{ mg_alts = L _ alts }))
  = sep [ sep [text "case", nest 4 (ppr expr), text "of"]
        , pp_alts
        ]
  where
    pp_alts | null alts = text "{}"
            | otherwise = nest 2 (pprMatches matches)
ppr_expr (CsIf _ e1 e2 e3)
  = sep [ hsep [text "if", nest 2 (ppr e1), text "then"]
        , nest 4 (ppr e2)
        , text "else"
        , nest 4 (ppr e3)
        ]
ppr_expr (CsMultiIf _ alts)
  = hang (text "if") 3 (vcat (map ppr_alt alts))
  where ppr_alt (L _ (GRHS _ guards expr))
          = hang vbar 2 (ppr_one one_alt)
          where
            ppr_one [] = panic "ppr_exp CsMultiIf"
            ppr_one (h:t) = hang h 2 (sep t)
            one_alt = [ interpp'SP guards
                      , text "->" <+> pprDeeper (ppr expr) ]
ppr_expr (ExprWithTySig _ expr sig)
  = hang (nest 2 (ppr_lexpr expr) <+> dcolon)
         4 (ppr sig)

ppr_infix_expr :: (OutputableBndrId p) => CsExpr (CsPass p) -> Maybe SDoc
ppr_infix_expr (CsVar _ (L _ v)) = Just (pprInfixOcc v)
ppr_infix_expr (CsUnboundVar _ occ) = Just (pprInfixOcc occ)
ppr_infix_expr _ = Nothing

ppr_apps
  :: (OutputableBndrId p)
  => CsExpr (CsPass p)
  -> [(LCsExpr (CsPass p))]
  -> SDoc
ppr_apps (CsApp _ (L _ fun) arg) args = ppr_apps fun (arg:args)
ppr_apps fun args = hang (ppr_expr fun) 2 (fsep (map ppr args))

ppr_tyapps
  :: (OutputableBndrId p)
  => CsExpr (CsPass p)
  -> [(LCsExpr (CsPass p))]
  -> SDoc
ppr_tyapps (CsTyApp _ (L _ fun) arg) args = ppr_tyapps fun (arg:args)
ppr_tyapps fun args = hang (ppr_expr fun) 2 (fsep (map ppr args))

pprDebugParendExpr
  :: (OutputableBndrId p)
  => PprPrec -> LCsExpr (CsPass p)
  -> SDoc
pprDebugParendExpr p expr
  = getPprDebug $ \case
  True -> pprParendLExpr p expr
  False -> pprLExpr expr

pprParendLExpr
  :: (OutputableBndrId p)
  => PprPrec -> LCsExpr (CsPass p) -> SDoc
pprParendLExpr p (L _ e) = pprParendExpr p e

pprParendExpr
  :: (OutputableBndrId p)
  => PprPrec -> CsExpr (CsPass p) -> SDoc
pprParendExpr p expr
  | csExprNeedsParens p expr = parens (pprExpr expr)
  | otherwise = pprExpr expr

csExprNeedsParens :: IsPass p => PprPrec -> CsExpr (CsPass p) -> Bool
csExprNeedsParens prec = go
  where
    go :: CsExpr (CsPass p) -> Bool
    go (CsVar{}) = False
    go (CsUnboundVar{}) = False
    go (CsLit _ l) = csLitNeedsParens prec l
    go (CsLam{}) = prec > topPrec
    go (CsApp{}) = prec >= appPrec
    go (CsTyLam{}) = prec > topPrec
    go (CsTyApp{}) = prec >= appPrec
    go (OpApp{}) = prec >= opPrec
    go (CsPar{}) = False
    go (SectionL{}) = True
    go (SectionR{}) = True
    go (ExplicitTuple{}) = prec >= appPrec
    go (ExplicitSum{}) = False
    go (CsCase{}) = prec > topPrec
    go (CsIf{}) = prec > topPrec
    go (CsMultiIf{}) = prec > topPrec
    go (ExprWithTySig{}) = prec >= sigPrec

isAtomicCsExpr :: IsPass p => CsExpr (CsPass p) -> Bool
isAtomicCsExpr (CsVar{}) = True
isAtomicCsExpr (CsUnboundVar{}) = True
isAtomicCsExpr (CsLit{}) = True
isAtomicCsExpr _ = False

pprMatches
  :: (OutputableBndrId idR, Outputable body)
  => MatchGroup (CsPass idR) body
  -> SDoc
pprMatches MG{ mg_alts = matches } = vcat (map pprMatch (map unLoc (unLoc matches)))

pprMatch
  :: (OutputableBndrId idR, Outputable body)
  => Match (CsPass idR) body
  -> SDoc
pprMatch (Match{ m_pats = pats, m_ctxt = ctxt, m_grhss = grhss })
  = sep [ sep (herald : map (nest 2 . pprParendLPat appPrec) other_pats)
        , nest 2 (pprGRHSs ctxt grhss) ]
  where
    (herald, other_pats)
      = case ctxt of
          LamAlt -> (char '\\', pats)
          TLamAlt -> (char '\\', pats)
          _ -> case pats of
                 [] -> (empty, [])
                 [pat] -> (ppr pat, [])
                 _ -> pprPanic "pprMatch" (ppr ctxt $$ ppr pats)

pprGRHSs
  :: (OutputableBndrId idR, Outputable body)
  => CsMatchContext fn
  -> GRHSs (CsPass idR) body
  -> SDoc
pprGRHSs ctxt (GRHSs _ grhss) = vcat (map (pprGRHS ctxt . unLoc) grhss)

pprGRHS
  :: (OutputableBndrId idR, Outputable body)
  => CsMatchContext fn
  -> GRHS (CsPass idR) body
  -> SDoc
pprGRHS ctxt (GRHS _ [] body) = pp_rhs ctxt body
pprGRHS ctxt (GRHS _ guards body) = sep [ vbar <+> interpp'SP guards
                                        , pp_rhs ctxt body ]

pp_rhs :: Outputable body => CsMatchContext fn -> body -> SDoc
pp_rhs ctxt rhs = matchSeparator ctxt <+> pprDeeper (ppr rhs)

matchSeparator :: CsMatchContext fn -> SDoc
matchSeparator _ = text "->"

instance (OutputableBndrId pl, OutputableBndrId pr,
           Anno (StmtLR (CsPass pl) (CsPass pr) body) ~ SrcSpanAnnA,
           Outputable body)
  => Outputable (StmtLR (CsPass pl) (CsPass pr) body) where
  ppr stmt = pprStmt stmt

pprStmt
  :: (OutputableBndrId idL,
      OutputableBndrId idR,
      Anno (StmtLR (CsPass idL) (CsPass idR) body) ~ SrcSpanAnnA,
      Outputable body)
  => (StmtLR (CsPass idL) (CsPass idR) body) -> SDoc
pprStmt (GuardBodyStmt _ expr) = ppr expr

instance Outputable fn => Outputable (CsMatchContext fn) where
  ppr LamAlt = text "LamAlt"
  ppr TLamAlt = text "TLamAlt"
  ppr CaseAlt = text "CaseAlt"
  ppr MultiIfAlt = text "MultiIfAlt"

type instance Anno (CsExpr (CsPass p)) = SrcSpanAnnA
type instance Anno [LocatedA (Match (CsPass p) (LocatedA (CsExpr (CsPass p))))] = SrcSpanAnnL
type instance Anno (Match (CsPass p) (LocatedA (CsExpr (CsPass p)))) = SrcSpanAnnA
type instance Anno (GRHS (CsPass p) (LocatedA (CsExpr (CsPass p)))) = EpAnnCO
type instance Anno (StmtLR (CsPass pl) (CsPass pr) (LocatedA (body (CsPass pr)))) = SrcSpanAnnA

type instance Anno FastString = EpAnnCO

instance (HasAnnotation (Anno a)) => WrapXRec (CsPass p) a where
  wrapXRec = noLocA
