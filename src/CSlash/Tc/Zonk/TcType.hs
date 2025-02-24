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
                    Writing to metavariables
*                                                                      *
********************************************************************* -}

writeMetaKiVar :: HasDebugCallStack => TcKiVar -> TcKind -> ZonkM ()
writeMetaKiVar kivar ki
  | not debugIsOn
  = writeMetaKiVarRef kivar (metaKiVarRef kivar) ki
  | not (isTcKiVar kivar)
  = massertPpr False (text "Writing to non-tc kivar" <+> ppr kivar)
  | MetaKv { mkv_ref = ref } <- tcKiVarDetails kivar
  = writeMetaKiVarRef kivar ref ki
  | otherwise
  = massertPpr False (text "Writing to non-meta kivar" <+> ppr kivar)
{-# INLINE writeMetaKiVar #-}

writeMetaKiVarRef :: HasDebugCallStack => TcKiVar -> TcRef MetaDetailsK -> TcKind -> ZonkM ()
writeMetaKiVarRef kivar ref ki
  | not debugIsOn
  = do traceZonk "writeMetaKiVar" (ppr kivar <+> text ":=" <+> ppr ki)
       writeTcRef ref (Indirect ki)
  | otherwise
  = do meta_details <- readTcRef ref
       zonked_ki <- zonkTcKind ki
       let zonked_ki_lvl = tcKindLevel zonked_ki
           kv_lvl = tcKiVarLevel kivar
           level_check_ok = not (zonked_ki_lvl `strictlyDeeperThan` kv_lvl)
           level_check_msg = ppr zonked_ki_lvl $$ ppr kv_lvl
                             $$ ppr kivar $$ ppr ki $$ ppr zonked_ki

       traceZonk "writeMetaKiVar" (ppr kivar <+> text ":=" <+> ppr ki)

       massertPpr (isFlexi meta_details) (double_upd_msg meta_details)

       massertPpr level_check_ok level_check_msg

       writeTcRef ref (Indirect ki)
   where
     double_upd_msg details = hang (text "Double update of meta kivar")
                              2 (ppr kivar $$ ppr details)
{-# INLINE writeMetaKiVarRef #-}

{- *********************************************************************
*                                                                      *
              Zonking 
*                                                                      *
********************************************************************* -}

zonkTcType :: TcType -> ZonkM TcType
zonkTcType = panic "zonkTcType"

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

zonkTcTyVarsToTcTyVars :: HasDebugCallStack => [TcTyVar] -> ZonkM [TcTyVar]
zonkTcTyVarsToTcTyVars = mapM zonkTcTyVarToTcTyVar

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

zonkTcKind :: TcKind -> ZonkM TcKind
zonkTcKinds :: [TcKind] -> ZonkM [TcKind]
(zonkTcKind, zonkTcKinds) = mapKind zonkTcKindMapper

zonkTcKindMapper :: KindMapper () ZonkM
zonkTcKindMapper = KindMapper
  { km_kivar = const zonkTcKiVar
  , km_UKd = const $ return UKd
  , km_AKd = const $ return AKd
  , km_LKd = const $ return LKd
  }

zonkTcKiVar :: TcKiVar -> ZonkM TcKind
zonkTcKiVar kv = do
  massertPpr (isTcKiVar kv) (ppr kv)
  case tcKiVarDetails kv of
    SkolemKv {} -> return $ mkKiVarKi kv
    MetaKv { mkv_ref = ref } -> do
      cts <- readTcRef ref
      case cts of
        Flexi -> return $ mkKiVarKi kv
        Indirect ki -> do
          zki <- zonkTcKind ki
          writeTcRef ref (Indirect zki)
          return zki

zonkTcKiVarsToTcKiVars :: HasDebugCallStack => [TcKiVar] -> ZonkM [TcKiVar]
zonkTcKiVarsToTcKiVars = mapM zonkTcKiVarToTcKiVar

zonkTcKiVarToTcKiVar :: HasDebugCallStack => TcKiVar -> ZonkM TcKiVar
zonkTcKiVarToTcKiVar kv = do
  ki <- zonkTcKiVar kv
  let kv' = case getKiVar_maybe ki of
              Just kv' -> kv'
              Nothing -> pprPanic "zonkTcKiVarToTcKiVar" (ppr kv $$ ppr ki)
  return kv'

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
