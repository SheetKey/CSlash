module CSlash.Cs.Expr
  ( module CSlash.Language.Syntax.Expr
  , module CSlash.Cs.Expr
  ) where

import CSlash.Language.Syntax.Expr
import CSlash.Language.Syntax.Extension

import CSlash.Utils.Outputable

instance (OutputableBndrId p) => Outputable (CsExpr (CsPass p)) where
  ppr expr = pprExpr expr

pprExpr :: (OutputableBndrId p) => CsExpr (CsPass p) -> SDoc
pprExpr e | isAtomicCsExpr e || isQuietCsExpr e = ppr_expr e
          | otherwise = pprDeeper (ppr_expr e)

isQuietCsExpr :: CsExpr id -> Bool
isQuietCsExpr (CsPar {}) = True
isQuietCsExpr (CsApp {}) = True
isQuietCsExpr (CsAppType {}) = True
isQuietCsExpr (OpApp {}) = True
isQuietCsExpr _ = False

ppr_lexpr :: (OutputableBndrId p) => LCsExpr (CsPass p) -> SDoc
ppr_lexpr e = ppr_expr (unLoc e)

ppr_expr
  :: forall p. (OutputableBndrId p)
  => CsExpr (CsPass p)
  -> SDoc
ppr_expr (CsVar _ (L _ v)) = pprPrefixOcc v
ppr_expr (CsUnboundVar _ uv) = pprPrefixOcc uv
ppr_expr (CsLit _ lit) = ppr lit
ppr_expr (CsLam _ matches) = pprMatches matches
ppr_expr e@(CsApp {}) = ppr_apps e []
ppr_expr (CsTyLam _ matches) = pprMathces matches
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
            | otherwise = nest 2 (pprMatches mathces)
ppr_expr (CsIf _ e1 e2 e3)
  = sep [ hsep [text "if", nest 2 (ppr e1), text "then"]
        , hsep 4 (ppr e2)
        , text "else"
        , nest 4 (ppr e3)
        ]
ppr_expr (CsMultiIf _ alts)
  = hand (text "if") 3 (vcat (map ppr_alt alts))
  where ppr_alt (L _ (GRHS _ guards expr))
          = hang vbar 2 (ppr_one one_alt)
          where
            ppr_one [] = panic "ppr_exp CsMultiIf"
            ppr_one (h:t) = hand h 2 (sep t)
            one_alt = [ interpp'SP guards
                      , text "->" <+> pprDeeper (ppr expr) ]
ppr_expr (ExprWithTySig _ expr sig)
  = hang (nest 2 (ppr_lexpr expr) <+> dcolon)
         4 (ppr sig)
