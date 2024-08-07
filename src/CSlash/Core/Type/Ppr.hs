module CSlash.Core.Type.Ppr where

import CSlash.Core.Type.Rep
import CSlash.Types.Var
-- import CSlash.Iface.Type

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Types.Basic


pprType :: Type -> SDoc
pprType = undefined -- pprPrecType topPrec

-- pprPrecType :: PprPrec -> Type -> SDoc
-- pprPreType = pprPrecTypeX emptyTidyEnv

-- pprPrecTypeX :: TidyEnv -> PprPrec -> Type -> SDoc
-- pprPrecTypeX env prec ty
--   = getPprStyle $ \ sty ->
--     getPprDebug $ \ debug ->
--                     if debug
--                     then debug_ppr_ty prec ty
--                     else pprPrecIfaceType prec (tidyToIfaceTypeStyX env ty sty)

-- tidyToIfaceTypeStyX :: TidyEnv -> Type -> PprStyle -> IfaceType
-- tidyToIfaceTypeStyX env ty sty
--   | useStyle sty = tidyToIfaceTypeX env ty
--   | otherwise = toIfaceTypeX (tyVarsOfType ty) ty

-- tidyToIfaceTypeX :: TidyEnv -> Type -> IfaceType
-- tidyToIfaceTypeX env ty = toIfaceTypeX (mkVarSet free_tvs) (tidyType env' ty)
--   where
--     env' = tidyFreeTyVars env free_tvs
--     free_tvs = tyVarsOfTypeWellScoped ty

pprTyVar :: TypeVar -> SDoc
pprTyVar tv = parens (ppr tv <+> colon <+> ppr kind)
  where
    kind = varKind tv
