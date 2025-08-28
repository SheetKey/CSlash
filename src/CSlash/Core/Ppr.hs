{-# LANGUAGE MultiWayIf #-}

module CSlash.Core.Ppr where

import Prelude hiding ((<>))

import CSlash.Core
import CSlash.Types.Fixity (LexicalFixity(..))
import CSlash.Types.Name( pprInfixName, pprPrefixName )
import CSlash.Types.Var
import CSlash.Types.Id
import CSlash.Types.Id.Info
import CSlash.Core.DataCon
import CSlash.Core.TyCon
import CSlash.Core.Type.Ppr
import CSlash.Types.Basic
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Types.SrcLoc ( pprUserRealSpan )
import CSlash.Types.Tickish

pprCoreExpr :: OutputableBndr b => Expr b -> SDoc
pprCoreExpr = undefined

instance OutputableBndr b => Outputable (Expr b) where
  ppr expr = pprCoreExpr expr

instance IsTyVar tv kv => OutputableBndr (Var tv kv) where
  pprBndr = undefined
  pprInfixOcc = pprInfixName . varName
  pprPrefixOcc = pprInfixName . varName
  bndrIsJoin_maybe = undefined

instance IsTyVar tv kv => OutputableBndr (Id tv kv) where
  pprBndr = pprCoreBinder
  pprInfixOcc = pprInfixName . varName
  pprPrefixOcc = pprPrefixName . varName
  bndrIsJoin_maybe = undefined

pprOcc :: OutputableBndr a => LexicalFixity -> a -> SDoc
pprOcc Infix = pprInfixOcc
pprOcc Prefix = pprPrefixOcc

pprCoreBinder :: IsTyVar tv kv => BindingSite -> Id tv kv -> SDoc
pprCoreBinder LetBind binder = pprTypedLetBinder binder $$ ppIdInfo binder (idInfo binder)
pprCoreBinder bind_site bndr = getPprDebug $ \debug -> pprTypedLamBinder bind_site debug bndr

pprUntypedBinder :: IsTyVar tv kv => Id tv kv -> SDoc
pprUntypedBinder binder = pprIdBndr binder

pprTypedLamBinder :: IsTyVar tv kv => BindingSite -> Bool -> Id tv kv -> SDoc
pprTypedLamBinder bind_site debug_on var
  = sdocOption sdocSuppressTypeSignatures $ \suppress_sigs -> 
    if | not debug_on
       , CaseBind <- bind_site
       , isDeadBinder var -> empty

       | not debug_on
       , isDeadBinder var -> char '_' <+> pprIdBndrInfo (idInfo var)

       | not debug_on
       , CaseBind <- bind_site -> pprUntypedBinder var

       | not debug_on
       , CasePatBind <- bind_site -> pprUntypedBinder var

       | suppress_sigs -> pprUntypedBinder var

       | otherwise -> parens (hang (pprIdBndr var)
                              2 (vcat [ colon <+> pprType (varType var)
                                      , pp_unf ]))
  where
    unf_info = realUnfoldingInfo (idInfo var)
    pp_unf | hasSomeUnfolding unf_info = text "Unh=" <> ppr unf_info
           | otherwise = empty

pprTypedLetBinder :: IsTyVar tv kv => Id tv kv -> SDoc
pprTypedLetBinder binder
  = sdocOption sdocSuppressTypeSignatures $ \suppress_sigs ->
    if suppress_sigs
    then pprIdBndr binder
    else hang (pprIdBndr binder) 2 (colon <+> pprType (varType binder))

pprIdBndr :: IsTyVar tv kv => Id tv kv -> SDoc
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

ppIdInfo :: IsTyVar tv kv => Id tv kv -> IdInfo -> SDoc
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
                , text "Guaance=" <> ppr g ]
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
