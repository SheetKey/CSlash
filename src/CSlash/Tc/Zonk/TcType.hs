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
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.TcRef
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Types.BasicTypes
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Zonk.Monad

-- import GHC.Core.InstEnv (ClsInst(is_tys))
import CSlash.Core.Type.Rep
import CSlash.Core.Type.Tidy
import CSlash.Core.TyCon
import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Core.Kind.Compare
-- import GHC.Core.Coercion
import CSlash.Core.Predicate

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

writeMetaTyVar :: HasDebugCallStack => TcTyVar -> TcType -> ZonkM ()
writeMetaTyVar = undefined

writeMetaTyVarRef :: HasDebugCallStack => TcTyVar -> TcRef MetaDetails -> TcType -> ZonkM ()
writeMetaTyVarRef tyvar ref ty
  | not debugIsOn
  = do traceZonk "writeMetaTyVar" (ppr tyvar <+> colon <+> ppr (tyVarKind tyvar)
                                   <+> text ":=" <+> ppr ty)
       writeTcRef ref (Indirect ty)
  | otherwise
  = do meta_details <- readTcRef ref
       let tv_kind = tyVarKind tyvar
           tv_lvl = tcTyVarLevel tyvar
       zonked_tv_kind <- zonkTcMonoKind tv_kind
       zonked_ty <- zonkTcType ty
       let zonked_ty_kind = typeKind zonked_ty
           zonked_ty_lvl = tcTypeLevel zonked_ty
           level_check_ok = not (zonked_ty_lvl `strictlyDeeperThan` tv_lvl)
           level_check_msg = ppr zonked_ty_lvl $$ ppr tv_lvl
                             $$ ppr tyvar $$ ppr ty $$ ppr zonked_ty
           kind_check_ok = zonked_ty_kind `eqKind` Mono zonked_tv_kind
           kind_msg = hang (text "Ill-kinded update to meta tyvar")
                           2 (ppr tyvar <+> colon <+> (ppr tv_kind $$ ppr zonked_tv_kind)
                              <+> text ":="
                              <+> ppr ty <+> colon <+> (ppr zonked_ty_kind))
       traceZonk "writeMetaTyVar" (ppr tyvar <+> text ":=" <+> ppr ty)

       massertPpr (isFlexi meta_details) (double_upd_msg meta_details)

       massertPpr level_check_ok level_check_msg

       massertPpr kind_check_ok kind_msg

       writeTcRef ref (Indirect ty)
  where
    double_upd_msg details = hang (text "Double update of meta tyvar")
                                  2 (ppr tyvar $$ ppr details)
{-# INLINE writeMetaTyVarRef #-}

writeMetaKiVar :: HasDebugCallStack => TcKiVar -> TcMonoKind -> ZonkM ()
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

writeMetaKiVarRef :: HasDebugCallStack => TcKiVar -> TcRef MetaDetailsK -> TcMonoKind -> ZonkM ()
writeMetaKiVarRef kivar ref ki
  | not debugIsOn
  = do traceZonk "writeMetaKiVar" (ppr kivar <+> text ":=" <+> ppr ki)
       writeTcRef ref (Indirect ki)
  | otherwise
  = do meta_details <- readTcRef ref
       zonked_ki <- zonkTcMonoKind ki
       let zonked_ki_lvl = tcMonoKindLevel zonked_ki
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
zonkTcTypes :: [TcType] -> ZonkM [TcType]
(zonkTcType, zonkTcTypes) = mapType zonkTcTypeMapper
  where
    zonkTcTypeMapper :: TypeMapper () ZonkM
    zonkTcTypeMapper = TypeMapper
      { tcm_tyvar = const zonkTcTyVar
      , tcm_tybinder = \_ tv _ k -> zonkTyVarKind tv >>= k ()
      , tcm_tylambinder = \_ tv k -> zonkTyVarKind tv >>= k ()
      , tcm_tylamkibinder = \_ kv k -> k () kv
      , tcm_tycon = zonkTcTyCon
      , tcm_embed_mono_ki = const zonkTcMonoKind
      }

zonkTcTyCon :: TcTyCon -> ZonkM TcTyCon
zonkTcTyCon tc
  | isMonoTcTyCon tc = do tck' <- zonkTcKind (tyConKind tc)
                          return $ setTcTyConKind tc tck'
  | otherwise = return tc

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
  kind' <- zonkTcMonoKind $ tyVarKind tv
  return $ setTyVarKind tv kind'

{- *********************************************************************
*                                                                      *
              Zonking kinds
*                                                                      *
********************************************************************* -}

zonkTcMonoKind :: TcMonoKind -> ZonkM TcMonoKind
zonkTcMonoKind ki = do
  ki' <- zonkTcKind $ Mono ki
  case ki' of
    Mono mki -> return mki
    _ -> pprPanic "zonkTcMonoKind" (ppr ki $$ ppr ki')

zonkTcKind :: TcKind -> ZonkM TcKind
zonkTcKinds :: [TcKind] -> ZonkM [TcKind]
(zonkTcKind, zonkTcKinds) = mapKind zonkTcKindMapper

zonkTcKindMapper :: KindMapper () ZonkM
zonkTcKindMapper = KindMapper
  { km_kivar = const zonkTcKiVar
  , km_kibinder = \_ kv k -> k () kv
  }

zonkTcKiVar :: TcKiVar -> ZonkM TcMonoKind
zonkTcKiVar kv 
  | isTcKiVar kv
  = case tcKiVarDetails kv of
      SkolemKv {} -> return $ mkKiVarMKi kv
      MetaKv { mkv_ref = ref } -> do
        cts <- readTcRef ref
        case cts of
          Flexi -> return $ mkKiVarMKi kv
          Indirect ki -> do
            zki <- zonkTcMonoKind ki
            writeTcRef ref (Indirect zki)
            return zki
  | otherwise
  = return $ mkKiVarMKi kv

zonkTcKiVarsToTcKiVars :: HasDebugCallStack => [TcKiVar] -> ZonkM [TcKiVar]
zonkTcKiVarsToTcKiVars = mapM zonkTcKiVarToTcKiVar

zonkTcKiVarToTcKiVar :: HasDebugCallStack => TcKiVar -> ZonkM TcKiVar
zonkTcKiVarToTcKiVar kv = do
  ki <- zonkTcKiVar kv
  let kv' = case getKiVarMono_maybe ki of
              Just kv' -> kv'
              Nothing -> pprPanic "zonkTcKiVarToTcKiVar" (ppr kv $$ ppr ki)
  return kv'

{- *********************************************************************
*                                                                      *
              Zonking constraints
*                                                                      *
********************************************************************* -}

zonkImplication :: Implication -> ZonkM Implication
zonkImplication implic@(Implic { ic_skols = skols, ic_wanted = wanted, ic_info = info }) = do
  skols' <- mapM zonkTyVarKind skols
  info' <- zonkSkolemInfoAnon info
  wanted' <- zonkWCRec wanted
  return $ implic { ic_skols = skols', ic_wanted = wanted', ic_info = info' }

zonkWC :: WantedConstraints -> ZonkM WantedConstraints
zonkWC wc = zonkWCRec wc

zonkWCRec :: WantedConstraints -> ZonkM WantedConstraints
zonkWCRec (WC { wc_simple = simple, wc_impl = implic }) = do
  simple' <- zonkSimples simple
  implic' <- mapBagM zonkImplication implic
  return $ WC { wc_simple = simple', wc_impl = implic' }

zonkSimples :: Cts -> ZonkM Cts
zonkSimples cts = do
  cts' <- mapBagM zonkCt cts
  traceZonk "zonkSimples dont:" (ppr cts')
  return cts'

zonkCt :: Ct -> ZonkM Ct
zonkCt (CRelCan rel@(RelCt { rl_ev = ev, rl_ki1 = k1, rl_ki2 = k2 })) = do
  ev' <- zonkCtEvidence ev
  k1' <- zonkTcMonoKind k1
  k2' <- zonkTcMonoKind k2
  return $ CRelCan $ rel { rl_ev = ev', rl_ki1 = k1', rl_ki2 = k2' }
zonkCt (CEqCan (KiEqCt { eq_ev = ev })) = mkNonCanonical <$> zonkCtEvidence ev
zonkCt (CIrredCan ir@(IrredCt { ir_ev = ev })) = do
  ev' <- zonkCtEvidence ev
  return $ CIrredCan $ ir { ir_ev = ev' }
zonkCt ct = do
  fl' <- zonkCtEvidence (ctEvidence ct)
  return $ mkNonCanonical fl'

zonkCtEvidence :: CtEvidence -> ZonkM CtEvidence
zonkCtEvidence ctev = do
  let pred = ctev_pred ctev
  pred' <- zonkTcMonoKind pred
  return $ setCtEvPredKind ctev pred'

zonkSkolemInfoAnon :: SkolemInfoAnon -> ZonkM SkolemInfoAnon
zonkSkolemInfoAnon (SigSkol cx ty tv_prs) = do
  ty' <- zonkTcType ty
  return $ SigSkol cx ty' tv_prs
zonkSkolemInfoAnon (InferSkol ntys) = do
  ntys' <- mapM do_one ntys
  return $ InferSkol ntys'
  where
    do_one (n, ty) = do
      ty' <- zonkTcType ty
      return (n, ty')
zonkSkolemInfoAnon skol_info = return skol_info

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

tcInitOpenTidyEnv :: [Var] -> ZonkM TidyEnv
tcInitOpenTidyEnv vs = do
  env1 <- tcInitTidyEnv
  let env2 = tidyFreeTyKiVars env1 vs
  return env2

tidyCt :: TidyEnv -> Ct -> Ct
tidyCt env = updCtEvidence (tidyCtEvidence env)

tidyCtEvidence :: TidyEnv -> CtEvidence -> CtEvidence
tidyCtEvidence env ctev = ctev { ctev_pred = tidyMonoKind env ki }
  where
    ki = ctev_pred ctev
