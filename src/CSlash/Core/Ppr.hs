{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiWayIf #-}

module CSlash.Core.Ppr where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Core as Core
import CSlash.Core.Stats (exprStats)
import CSlash.Types.Fixity (LexicalFixity(..))
import CSlash.Types.Name( pprInfixName, pprPrefixName )
import CSlash.Types.Var
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Core.DataCon
import CSlash.Core.TyCon
import CSlash.Core.Type
import CSlash.Core.Type.Ppr
import CSlash.Core.Type.Rep
import CSlash.Core.Kind
import CSlash.Types.Basic
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Types.SrcLoc ( pprUserRealSpan )
import CSlash.Types.Tickish

import CSlash.Utils.Panic

{- *********************************************************************
*                                                                      *
                Public interfaces for Core printing
*                                                                      *
********************************************************************* -}

pprCoreBindings :: (OutputableBndr b1, OutputableBndr b2) => [Bind b1 b2] -> SDoc
pprCoreBindings = pprTopBinds noAnn

pprCoreBindingsWithSize :: [CoreBind] -> SDoc
pprCoreBindingsWithSize = pprTopBinds sizeAnn

pprCoreExpr :: (OutputableBndr b1, OutputableBndr b2) => Expr b1 b2 -> SDoc
pprCoreExpr expr = ppr_expr noParens expr

pprParendExpr :: (OutputableBndr b1, OutputableBndr b2) => Expr b1 b2 -> SDoc
pprParendExpr expr = ppr_expr parens expr

instance (OutputableBndr b1, OutputableBndr b2) => Outputable (Bind b1 b2) where
  ppr bind = ppr_bind noAnn bind

instance (OutputableBndr b1, OutputableBndr b2) => Outputable (Expr b1 b2) where
  ppr expr = pprCoreExpr expr

instance (OutputableBndr b1, OutputableBndr b2) => Outputable (Alt b1 b2) where
  ppr expr = pprCoreAlt expr

{- *********************************************************************
*                                                                      *
                The guts
*                                                                      *
********************************************************************* -}

type Annotation b1 b2 = Expr b1 b2 -> SDoc

sizeAnn :: CoreExpr -> SDoc
sizeAnn e = text "-- RHS size:" <+> ppr (exprStats e)

noAnn :: Expr b1 b2 -> SDoc
noAnn _ = empty

pprTopBinds
  :: (OutputableBndr a, OutputableBndr b)
  => Annotation a b
  -> [Bind a b]
  -> SDoc
pprTopBinds ann binds = vcat (map (pprTopBind ann) binds)
 
pprTopBind :: (OutputableBndr a, OutputableBndr b) => Annotation a b -> Bind a b -> SDoc
pprTopBind ann (NonRec binder expr) = ppr_let_binding ann (binder, expr) $$ blankLine
pprTopBind _ (Rec []) = text "Rec { }"
pprTopBind ann (Rec (b:bs))
  = vcat [ text "Rec {"
         , ppr_let_binding ann b
         , vcat [ blankLine $$ ppr_let_binding ann b | b <- bs]
         , text "end Rec }"
         , blankLine ]

ppr_bind :: (OutputableBndr a, OutputableBndr b) => Annotation a b -> Bind a b -> SDoc
ppr_bind ann (NonRec val_bndr expr) = ppr_let_binding ann (val_bndr, expr)
ppr_bind ann (Rec binds) = vcat (map pp binds) where pp bind = ppr_let_binding ann bind <> semi

ppr_let_binding :: (OutputableBndr a, OutputableBndr b) => Annotation a b -> (b, Expr a b) -> SDoc
ppr_let_binding ann (val_bndr, expr)
  = vcat [ ann expr
         , ppUnlessOption sdocSuppressTypeSignatures
           (pprBndr LetBind val_bndr)
         , pp_bind ]
  where
    pp_val_bndr = pprPrefixOcc val_bndr

    pp_bind = case bndrIsJoin_maybe val_bndr of
                NotJoinPoint -> pp_normal_bind
                JoinPoint ar -> pp_join_bind ar

    pp_normal_bind = hang pp_val_bndr 2 (equals <+> pprCoreExpr expr)

    pp_join_bind join_arity = panic "pp_join_bind"

ppr_lam_binding :: (OutputableBndr a, OutputableBndr b) => Annotation a b -> (a, Expr a b) -> SDoc
ppr_lam_binding ann (val_bndr, expr)
  = vcat [ ann expr
         , ppUnlessOption sdocSuppressTypeSignatures
           (pprBndr LetBind val_bndr)
         , pp_bind ]
  where
    pp_val_bndr = pprPrefixOcc val_bndr

    pp_bind = case bndrIsJoin_maybe val_bndr of
                NotJoinPoint -> pp_normal_bind
                JoinPoint ar -> pp_join_bind ar

    pp_normal_bind = hang pp_val_bndr 2 (equals <+> pprCoreExpr expr)

    pp_join_bind join_arity = panic "pp_join_bind"

noParens :: SDoc -> SDoc
noParens pp = pp

pprOptTyCo :: TypeCoercion Zk -> SDoc
pprOptTyCo co = sdocOption sdocSuppressCoercions $ \case
  True -> angleBrackets (text "TCo:" <> int (panic "tycoercionSize co")) <+> colon <+> co_type
  False -> parens $ sep [ppr co, colon <+> co_type ]
  where
    co_type = sdocOption sdocSuppressCoercionTypes $ \case
      True -> text "..."
      False -> panic "ppr (tycoercionType co)"

pprOptKiCo :: KindCoercion Zk -> SDoc
pprOptKiCo co = sdocOption sdocSuppressCoercions $ \case
  True -> angleBrackets (text "KCo:" <> int (panic "kicoercionSize co")) <+> colon <+> co_kind
  False -> parens $ sep [ppr co, colon <+> co_kind]
  where
    co_kind = sdocOption sdocSuppressCoercionTypes $ \case
      True -> text "..."
      False -> ppr (kiCoercionKind co)

ppr_id_occ :: (SDoc -> SDoc) -> Id Zk -> SDoc
ppr_id_occ add_par id
  | isJoinId id = add_par ((text "jump") <+> pp_id)
  | otherwise = pp_id
  where
    pp_id = ppr id

ppr_expr :: (OutputableBndr a, OutputableBndr b) => (SDoc -> SDoc) -> Expr a b -> SDoc
ppr_expr add_par (Var id) = ppr_id_occ add_par id
ppr_expr add_par (Type ty) = add_par (text "TYPE:" <+> ppr ty)
ppr_expr add_par (Kind ki) = add_par (text "KIND:" <+> ppr ki)
ppr_expr add_par (KiCo kco) = add_par (text "KCO:" <+> ppr kco)
ppr_expr add_par (Lit lit) = panic "pprLiteral add_par lit"
ppr_expr add_par (Cast expr co) = add_par $ sep
                                  [pprParendExpr expr, text "`cast`" <+> pprOptTyCo co]
ppr_expr add_par expr@(Lam {})
  -- = let (bndrs, body) = collectBinders expr
  --       (vars, ids) = panic "break isRuntimeVar bndrs"
  --   in add_par $
  --      hang (text "/\\" <+> sep (map (pprBndr LambdaBind) vars) <+> arrow
  --            <+> text "\\" <+> sep (map (pprBndr LambdaBind) ids) <+> arrow)
  --      2 (pprCoreExpr body)
  = let (bndrs_kis, body) = collectBinders expr
        bndrs = fst <$> bndrs_kis
    in add_par $
       hang (text "\\" <+> sep (map (pprBndr LambdaBind) bndrs) <+> arrow)
       2 (pprCoreExpr body)

ppr_expr add_par expr@(App {})
  = sdocOption sdocSuppressTypeApplications $ \supp_ty_app ->
    case collectArgs expr of
      (fun, args) -> let pp_args = sep (map pprArg args)
                         val_args = dropWhile isNonValArg args
                         pp_tup_args = pprWithCommas pprCoreExpr val_args
                         args'
                           | supp_ty_app = val_args
                           | otherwise = args
                         parens
                           | null args' = id
                           | otherwise = add_par
                     in case fun of
                          Var f -> case isDataConId_maybe f of
                            Just dc | val_args `lengthIs` idArity f
                                    , isTupleTyCon (dataConTyCon dc)
                                    -> parens pp_tup_args
                            _ -> parens (hang fun_doc 2 pp_args)
                              where
                                fun_doc = ppr_id_occ noParens f
                          _ -> parens (hang (pprParendExpr fun) 2 pp_args)

ppr_expr add_par (Case expr _ ty []) = panic "empty case"

ppr_expr add_par (Case expr var ty [Alt con args rhs])
  = sdocOption sdocPrintCaseAsLet $ \case
      True -> panic "print case as let"
      False -> add_par $ sep [ sep [ sep [ text "case" <+> pprCoreExpr expr
                                         , whenPprDebug (text "return" <+> ppr ty)
                                         , text "of" <+> ppr_bndr var
                                         ]
                                   , char '{' <+> ppr_case_pat con args <+> arrow
                                   ]
                             , pprCoreExpr rhs
                             , char '}'
                             ]
  where
    ppr_bndr = pprBndr CaseBind

ppr_expr add_par (Case expr var ty alts)
  = add_par $ sep [ sep [ text "case"
                          <+> pprCoreExpr expr
                          <+> whenPprDebug (text "return" <+> ppr ty)
                        , text "of" <+> ppr_bndr var <+> char '{'
                        ]
                  , nest 2 (vcat (punctuate semi (map pprCoreAlt alts)))
                  , char '}'
                  ]
  where
    ppr_bndr = pprBndr CaseBind

ppr_expr add_par (Let bind expr)
  = add_par $
    sep [ hang (keyword bind <+> char '{') 2 (ppr_bind noAnn bind <+> text "} in ")
        , pprCoreExpr expr ]
  where
    keyword (NonRec b _)
      | isJoinPoint (bndrIsJoin_maybe b) = text "join"
      | otherwise = text "let"
    keyword (Rec pairs)
      | ((b, _):_) <- pairs
      , isJoinPoint (bndrIsJoin_maybe b) = text "joinrec"
      | otherwise = text "letrec"

ppr_expr add_par (Tick tickish expr)
  = sdocOption sdocSuppressTicks $ \case
      True | not (tickishIsCode tickish) -> ppr_expr add_par expr
      _ -> add_par (sep [ppr tickish, pprCoreExpr expr])

pprCoreAlt :: (OutputableBndr a, OutputableBndr b) => Alt a b -> SDoc
pprCoreAlt (Alt con args rhs)
  = hang (ppr_case_pat con args <+> arrow) 2 (pprCoreExpr rhs)

ppr_case_pat :: OutputableBndr a => AltCon -> [a] -> SDoc
ppr_case_pat (DataAlt dc) args
  | isTupleTyCon tc
  = parens (pprWithCommas ppr_bndr args)
  where
    ppr_bndr = pprBndr CasePatBind
    tc = dataConTyCon dc

ppr_case_pat con args
  = ppr con <+> (fsep (map ppr_bndr args))
  where ppr_bndr = pprBndr CasePatBind

pprArg :: (OutputableBndr a, OutputableBndr b) => Expr a b -> SDoc
pprArg (Type ty) = ppUnlessOption sdocSuppressTypeApplications
                   (braces (pprType ty))
pprArg (Kind ki) = ppUnlessOption sdocSuppressTypeApplications
                   (braces (pprMonoKind ki))
pprArg (KiCo co) = braces (char '~' <+> pprOptKiCo co)
pprArg expr = pprParendExpr expr

instance IsPass p => Outputable (CoreBndrP (CsPass p)) where
  ppr (Core.Id id) = ppr id
  ppr (Tv v) = ppr v
  ppr (KCv v) = ppr v
  ppr (Kv v) = ppr v

instance IsPass p => OutputableBndr (CoreBndrP (CsPass p)) where
  pprBndr = pprCoreBinder

  pprInfixOcc (Core.Id id) = pprInfixOcc id
  pprInfixOcc (Tv v) = pprInfixOcc v
  pprInfixOcc (KCv v) = pprInfixOcc v
  pprInfixOcc (Kv v) = pprInfixOcc v

  pprPrefixOcc (Core.Id id) = pprPrefixOcc id
  pprPrefixOcc (Tv v) = pprPrefixOcc v
  pprPrefixOcc (KCv v) = pprPrefixOcc v
  pprPrefixOcc (Kv v) = pprPrefixOcc v

  bndrIsJoin_maybe (Core.Id id) = idJoinPointHood id
  bndrIsJoin_maybe _ = NotJoinPoint

instance (OutputableBndr b, Outputable t) => OutputableBndr (TaggedBndr b t) where
  pprBndr _ b = ppr b
  pprInfixOcc b = ppr b
  pprPrefixOcc b = ppr b
  bndrIsJoin_maybe (TB b _) = bndrIsJoin_maybe b

instance IsPass p => OutputableBndr (Id (CsPass p)) where
  pprBndr b v = pprCoreBinder b (Core.Id v)
  pprInfixOcc = pprInfixName . varName
  pprPrefixOcc = pprPrefixName . varName
  bndrIsJoin_maybe = idJoinPointHood

instance IsPass p => OutputableBndr (TyVar (CsPass p)) where
  pprBndr b v = pprCoreBinder b (Tv v)
  pprInfixOcc = pprInfixName . varName
  pprPrefixOcc = pprPrefixName . varName
  bndrIsJoin_maybe _ = NotJoinPoint

instance IsPass p => OutputableBndr (KiCoVar (CsPass p)) where
  pprBndr b v = pprCoreBinder b (KCv v)
  pprInfixOcc = pprInfixName . varName
  pprPrefixOcc = pprPrefixName . varName
  bndrIsJoin_maybe _ = NotJoinPoint

instance IsPass p => OutputableBndr (KiVar (CsPass p)) where
  pprBndr b v = pprCoreBinder b (Kv v)
  pprInfixOcc = pprInfixName . varName
  pprPrefixOcc = pprPrefixName . varName
  bndrIsJoin_maybe _ = NotJoinPoint

pprOcc :: OutputableBndr a => LexicalFixity -> a -> SDoc
pprOcc Infix = pprInfixOcc
pprOcc Prefix = pprPrefixOcc

pprCoreBinder :: HasPass p pass => BindingSite -> CoreBndrP p -> SDoc
pprCoreBinder LetBind (Core.Id binder)
  = pprTypedLetBinder binder $$ ppIdInfo binder (idInfo binder)
pprCoreBinder bind_site bndr = getPprDebug $ \debug -> pprTypedLamBinder bind_site debug bndr

pprCoreBinders :: HasPass p pass => [CoreBndrP p] -> SDoc
pprCoreBinders vs = sep (map (pprCoreBinder LambdaBind) vs)

pprUntypedBinder :: HasPass p pass => CoreBndrP p -> SDoc
pprUntypedBinder (Core.Id binder) = pprIdBndr binder
pprUntypedBinder binder = pprPrefixOcc binder

pprTypedLamBinder :: HasPass p pass => BindingSite -> Bool -> CoreBndrP p -> SDoc
pprTypedLamBinder bind_site debug_on var
  = sdocOption sdocSuppressTypeSignatures $ \suppress_sigs -> 
    if | not debug_on
       , CaseBind <- bind_site
       , Core.Id id <- var
       , isDeadBinder id -> empty

       | not debug_on
       , Core.Id id <- var
       , isDeadBinder id -> char '_' <+> pprIdBndrInfo (idInfo id)

       | not debug_on
       , CaseBind <- bind_site -> pprUntypedBinder var

       | not debug_on
       , CasePatBind <- bind_site -> pprUntypedBinder var

       | suppress_sigs -> pprUntypedBinder var

       | otherwise -> parens (hang (pprUntypedBinder var)
                              2 (vcat [ pp_type_or_kind
                                      , pp_unf ]))
                          
  where
    unf_info_m | Core.Id id <- var = Just $ realUnfoldingInfo (idInfo id)
               | otherwise = Nothing
    pp_unf | Just unf_info <- unf_info_m
           , hasSomeUnfolding unf_info = text "Unh=" <> ppr unf_info
           | otherwise = empty
    pp_type_or_kind = case var of
      Core.Id id -> colon <+> pprType (varType id)
      Tv tv -> colon <+> pprMonoKind (varKind tv)
      KCv kcv -> colon <+> pprMonoKind (varKind kcv)
      Kv {} -> empty

pprTypedLetBinder :: HasPass p pass => Id p -> SDoc
pprTypedLetBinder binder
  = sdocOption sdocSuppressTypeSignatures $ \suppress_sigs ->
    if suppress_sigs
    then pprIdBndr binder
    else hang (pprIdBndr binder) 2 (colon <+> pprType (varType binder))

pprIdBndr :: HasPass p pass => Id p -> SDoc
pprIdBndr id = pprPrefixOcc id <+> pprIdBndrInfo (idInfo id)

pprIdBndrInfo :: IdInfo -> SDoc
pprIdBndrInfo info
  = ppUnlessOption sdocSuppressIdInfo (info `seq` doc)
  where
    occ_info = occInfo info
    lbv_info = oneShotInfo info

    has_occ = not (isNoOccInfo occ_info)
    has_lbv = not (hasNoOneShotInfo lbv_info)

    doc = showAttributes
          [ (has_occ, text "Occ=" <> ppr occ_info)
          , ( has_lbv, text "OS=" <> ppr lbv_info)
          ]

ppIdInfo :: Id p -> IdInfo -> SDoc
ppIdInfo id info
  = ppUnlessOption sdocSuppressIdInfo
    $ showAttributes
    [ (True, pp_scope <> ppr (idDetails id))
    , (has_arity, text "Arity=" <> int arity)
    , (has_called_arity, text "CallArity=" <> int called_arity)
    , (has_caf_info, text "Caf=" <> ppr caf_info)
    , (has_unf, text "Unf=" <> ppr unf_info)
    ]
  where
    pp_scope | isGlobalId id = text "GblId"
             | isExportedId id = text "LclIdX"
             | otherwise = text "LclId"

    arity = arityInfo info
    has_arity = arity /= 0

    called_arity = callArityInfo info
    has_called_arity = called_arity /= 0

    caf_info = cafInfo info
    has_caf_info = not (mayHaveCafRefs caf_info)

    unf_info = realUnfoldingInfo info
    has_unf = hasSomeUnfolding unf_info

showAttributes :: [(Bool, SDoc)] -> SDoc
showAttributes stuff
  | null docs = empty
  | otherwise = brackets (sep (punctuate comma docs))
  where docs = [d | (True, d) <- stuff]

instance Outputable UnfoldingGuidance where
  ppr UnfNever = text "NEVER"
  ppr (UnfWhen { ug_arity = arity, ug_unsat_ok = unsat_ok, ug_boring_ok = boring_ok })
    = text "ALWAYS_IF" <>
      parens (text "arity=" <> int arity <> comma <>
              text "unsat_ok=" <> ppr unsat_ok <> comma <>
              text "boring_ok=" <> ppr boring_ok)
  ppr (UnfIfGoodArgs { ug_args = cs, ug_size = size, ug_res = discount })
    = hsep [ text "IF_ARGS"
           , brackets (hsep (map int cs))
           , int size
           , int discount ]

instance Outputable Unfolding where
  ppr NoUnfolding = text "No unfolding"
  ppr (OtherCon cs) = text "OtherCon" <+> ppr cs
  ppr (CoreUnfolding { uf_src = src
                      , uf_tmpl = rhs
                      , uf_is_top = top
                      , uf_cache = cache
                      , uf_guidance = g })
    = text "Unf" <> braces (pp_info $$ pp_rhs)
    where
      pp_info = fsep $ punctuate comma
                [ text "Src=" <> ppr src
                , text "TopLvl=" <> ppr top
                , ppr cache
                , text "Guidance=" <> ppr g ]
      pp_tmpl = ppUnlessOption sdocSuppressUnfoldings (text "Tmpl=" <+> ppr rhs)
      pp_rhs | isStableSource src = pp_tmpl
             | otherwise = empty

instance Outputable UnfoldingCache where
  ppr (UnfoldingCache { uf_is_value = hnf, uf_is_conlike = conlike
                      , uf_is_work_free = wf, uf_expandable = exp })
    = fsep $ punctuate comma
      [ text "Value=" <> ppr hnf
      , text "ConLike=" <> ppr conlike
      , text "WorkFree=" <> ppr wf
      , text "Expandable=" <> ppr exp ]

{- --------------------------------------------------
--      Rules
-------------------------------------------------- -}

instance Outputable CoreRule where
  ppr = pprRule

pprRule :: CoreRule -> SDoc
pprRule BuiltinRule = text "Built in rule for"
pprRule Rule{ ru_name = name
            , ru_act = act
            , ru_fn = fn
            , ru_bndrs = tpl_vars
            , ru_args = tpl_args
            , ru_rhs = rhs }
  = hang (doubleQuotes (ftext name) <+> ppr act)
    4 (sep [ text "forall" <+> pprCoreBinders tpl_vars <> dot
           , nest 2 (ppr fn <+> sep (map pprArg tpl_args))
           , nest 2 (text "=" <+> pprCoreExpr rhs)
           ])
