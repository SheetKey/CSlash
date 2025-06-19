module CSlash.Core.Type.Ppr where

import Prelude hiding ((<>))

import CSlash.Core.Type
import CSlash.Core.Type.Rep
import CSlash.Core.Kind
import CSlash.Types.Var
import CSlash.Types.Var.Env
-- import CSlash.Iface.Type

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Types.Basic

pprType :: VarHasKind tv kv => Type tv kv -> SDoc
pprType = pprPrecType topPrec

pprPrecType :: VarHasKind tv kv => PprPrec -> Type tv kv -> SDoc
pprPrecType = pprPrecTypeX emptyTidyEnv

pprPrecTypeX :: VarHasKind tv kv => MkTidyEnv tv kv -> PprPrec -> Type tv kv -> SDoc
pprPrecTypeX env prec ty
  = getPprStyle $ \ sty ->
    getPprDebug $ \ debug ->
                    if debug
                    then debug_ppr_ty prec ty
                    else panic "pprPrecIfaceType prec (tidyToIfaceTypeStyX env ty sty)"

pprTyVars :: VarHasKind tv kv => [tv] -> SDoc
pprTyVars tvs = sep (map pprTyVar tvs)

pprTyVar :: VarHasKind tv kv => tv -> SDoc
pprTyVar tv = parens (ppr tv <+> colon <+> ppr kind)
  where
    kind = varKind tv

debug_ppr_ty :: VarHasKind tv kv => PprPrec -> Type tv kv -> SDoc

debug_ppr_ty _ (TyVarTy tv) = ppr tv

debug_ppr_ty prec (FunTy { ft_kind = kind, ft_arg = arg, ft_res = res })
  = maybeParen prec funPrec
    $ sep [ debug_ppr_ty funPrec arg
          , char '-' <> ppr kind <> char '>' <+> debug_ppr_ty prec res ]

debug_ppr_ty prec (TyConApp tc tys)
  | null tys = ppr tc
  | otherwise = maybeParen prec appPrec
                $ hang (ppr tc) 2 (sep (map (debug_ppr_ty appPrec) tys))

debug_ppr_ty _ (AppTy t1 t2) = hang (debug_ppr_ty appPrec t1) 2 (debug_ppr_ty appPrec t2)

debug_ppr_ty prec (CastTy ty co)
  = maybeParen prec topPrec
    $ hang (debug_ppr_ty topPrec ty) 2 (text "|>" <+> ppr co)

debug_ppr_ty prec t
  | (bndrs, body) <- splitForAllForAllTyBinders t
  , not (null bndrs)
  = maybeParen prec funPrec
    $ sep [ forAllLit <+> fsep (map ppr_bndr bndrs) <> dot
          , ppr body ]
  where
    ppr_bndr (Bndr tv Specified) = braces (ppr tv)
    ppr_bndr (Bndr tv Required) = ppr tv

debug_ppr_ty _ ForAllTy{} = panic "debug_ppr_ty ForAllTy"

debug_ppr_ty prec t
  | (bndrs, body) <- splitTyLamTyBinders t
  , not (null bndrs)
  = maybeParen prec funPrec
    $ sep [ lambda <+> fsep (map ppr_bndr bndrs) <> arrow
          , ppr body ]
  where
    ppr_bndr tv = parens (ppr tv)

debug_ppr_ty _ TyLamTy{} = panic "debug_ppr_ty TyLamTy"

debug_ppr_ty prec t
  | (bndrs, body) <- splitBigLamTyBinders t
  , not (null bndrs)
  = maybeParen prec funPrec
    $ sep [ biglambda <+> fsep (map ppr_bndr bndrs) <> arrow
          , ppr body ]
  where
    ppr_bndr kv = parens (ppr kv)

debug_ppr_ty _ BigTyLamTy{} = panic "debug_ppr_ty BigTyLamTy"

debug_ppr_ty _ (Embed ki) = ppr ki

debug_ppr_ty _ (KindCoercion co) = text "[KiCo]" <+> (ppr co)
