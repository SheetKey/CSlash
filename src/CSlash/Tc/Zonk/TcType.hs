module CSlash.Tc.Zonk.TcType
  ( module CSlash.Tc.Zonk.Monad
  ,  module CSlash.Tc.Zonk.TcType
  ) where

import CSlash.Types.Name
import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Unique.Set

import CSlash.Tc.Errors.Types
import CSlash.Tc.Errors.Ppr
-- import GHC.Tc.Types.Constraint
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.TcRef
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Types.BasicTypes
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Zonk.Monad

-- import GHC.Core.InstEnv (ClsInst(is_tys))
import CSlash.Core.Type.Rep
import CSlash.Core.TyCon
import CSlash.Core.Type
import CSlash.Core.Kind
-- import GHC.Core.Coercion
-- import GHC.Core.Predicate

import CSlash.Utils.Constants
import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Monad ( mapAccumLM )
import CSlash.Utils.Panic

import CSlash.Data.Bag
-- import GHC.Data.Pair

{- *********************************************************************
*                                                                      *
              Zonking 
*                                                                      *
********************************************************************* -}

zonkTcType :: TcType -> ZonkM TcType
zonkTcType = undefined

zonkTcTyVar :: TcTyVar -> ZonkM TcType
zonkTcTyVar tv
  | isTcTyVar tv
  = case tcTyVarDetails tv of
      SkolemTv{} -> zonk_kind_and_return
      MetaTv { mtv_ref = ref } -> do
        cts <- readTcRef ref
        case cts of
          Flexi -> zonk_kind_and_return
          Indirect ty -> do
            zty <- zonkTcType ty
            writeTcRef ref (Indirect zty)
            return zty
  | otherwise
  = zonk_kind_and_return
  where
    zonk_kind_and_return = do
      z_tv <- zonkTyVarKind tv
      return $ mkTyVarTy z_tv

zonkTcTyVarToTcTyVar :: HasDebugCallStack => TcTyVar -> ZonkM TcTyVar
zonkTcTyVarToTcTyVar tv = do
  ty <- zonkTcTyVar tv
  let tv' = case getTyVar_maybe ty of
              Just tv' -> tv'
              Nothing -> pprPanic "zonkTcTyVarToTcTyVar" (ppr tv $$ ppr ty)
  return tv'

{- *********************************************************************
*                                                                      *
              Zonking types
*                                                                      *
********************************************************************* -}

zonkTyVarKind :: TypeVar -> ZonkM TypeVar
zonkTyVarKind tv = do
  kind' <- zonkTcKind $ tyVarKind tv
  return $ setTyVarKind tv kind'

{- *********************************************************************
*                                                                      *
              Zonking kinds
*                                                                      *
********************************************************************* -}

zonkTcKind :: Kind -> ZonkM Kind
zonkTcKind kv = panic "zonkTcKind"

{- *********************************************************************
*                                                                      *
                 Tidying
*                                                                      *
********************************************************************** -}

tcInitTidyEnv :: ZonkM TidyEnv
tcInitTidyEnv = do
  ZonkGblEnv { zge_binder_stack = bndrs } <- getZonkGblEnv
  go emptyTidyEnv bndrs
  where
    go (env, subst) [] = return (env, subst)
    go (env, subst) (b : bs)
      | TcTvBndr name tyvar <- b
      = do let (env', occ') = tidyOccName env (nameOccName name)
               name' = tidyNameOcc name occ'
               tyvar1 = setTyVarName tyvar name'
           tyvar2 <- zonkTcTyVarToTcTyVar tyvar1
           go (env', extendVarEnv subst tyvar tyvar2) bs
      | otherwise
      = go (env, subst) bs
