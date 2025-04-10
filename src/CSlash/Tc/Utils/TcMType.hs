module CSlash.Tc.Utils.TcMType where

import CSlash.Cs
import CSlash.Platform

import CSlash.Driver.DynFlags

-- import {-# SOURCE #-} GHC.Tc.Utils.Unify( unifyInvisibleType, tcSubMult )
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.Constraint
-- import GHC.Tc.Types.Evidence
import CSlash.Tc.Utils.Monad        -- TcType, amongst others
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Errors.Types
-- import CSlash.Tc.Zonk.Type
import CSlash.Tc.Zonk.TcType

import CSlash.Builtin.Names

import CSlash.Core.ConLike
import CSlash.Core.DataCon
import CSlash.Core.Type.Rep
import CSlash.Core.Type.Ppr
import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Core.TyCon
-- import GHC.Core.Coercion
-- import GHC.Core.Class
-- import GHC.Core.Predicate
import CSlash.Core.UsageEnv

import CSlash.Types.Var
import CSlash.Types.Id as Id
import CSlash.Types.Name
import CSlash.Types.SourceText
import CSlash.Types.Var.Set

import CSlash.Builtin.Types
import CSlash.Types.Var.Env
import CSlash.Types.Unique.Set
import CSlash.Types.Basic ( TypeOrKind(..)
                          , NonStandardDefaultingStrategy(..)
                          , DefaultingStrategy(..), defaultNonStandardTyVars )

import CSlash.Data.FastString
import CSlash.Data.Bag

import CSlash.Utils.Misc
import CSlash.Utils.Trace
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Constants (debugIsOn)

import Control.Monad
import Data.IORef
import CSlash.Data.Maybe
import qualified Data.Semigroup as Semi
import CSlash.Types.Name.Reader

{- *********************************************************************
*                                                                      *
        Kind variables
*                                                                      *
********************************************************************* -}

newMetaKindVar :: TcM TcKind
newMetaKindVar = do
  details <- newMetaDetailsK TauKv
  name <- newMetaKiVarName (fsLit "k")
  let kv = mkTcKiVar name details
  traceTc "newMetaKindVar" (ppr kv)
  return (mkKiVarKi kv)

{- *********************************************************************
*                                                                      *
        Constraints
*                                                                      *
********************************************************************* -}

newImplication :: TcM Implication
newImplication = do
  env <- getLclEnv
  warn_inaccessible <- woptM Opt_WarnInaccessibleCode
  return $ (implicationPrototype (mkCtLocEnv env))
           { ic_warn_inaccessible = warn_inaccessible }

{- *********************************************************************
*                                                                      *
        MetaKvs
*                                                                      *
********************************************************************* -}

newMetaKiVarName :: FastString -> TcM Name
newMetaKiVarName str = newSysName (mkKiVarOccFS str)

cloneMetaKiVarName :: Name -> TcM Name
cloneMetaKiVarName name = newSysName (nameOccName name)

metaInfoToKiVarName :: MetaInfoK -> FastString
metaInfoToKiVarName meta_info = case meta_info of
  TauKv -> fsLit "kt"
  KiVarKv -> fsLit "k"

newAnonMetaKiVar :: MetaInfoK -> TcM TcKiVar
newAnonMetaKiVar mi = newNamedAnonMetaKiVar (metaInfoToKiVarName mi) mi

newNamedAnonMetaKiVar :: FastString -> MetaInfoK -> TcM TcKiVar
newNamedAnonMetaKiVar kivar_name meta_info = do
  name <- newMetaKiVarName kivar_name
  details <- newMetaDetailsK meta_info
  let kivar = mkTcKiVar name details
  traceTc "newAnonMetaKiVar" (ppr kivar)
  return kivar

newMetaDetails :: MetaInfo -> TcM TcTyVarDetails
newMetaDetails info = do
  ref <- newMutVar Flexi
  tclvl <- getTcLevel
  return $ MetaTv { mtv_info = info
                  , mtv_ref = ref
                  , mtv_tclvl = tclvl }

newMetaDetailsK :: MetaInfoK -> TcM TcKiVarDetails
newMetaDetailsK info = do
  ref <- newMutVar Flexi
  tclvl <- getTcLevel
  return (MetaKv { mkv_info = info, mkv_ref = ref, mkv_tclvl = tclvl })

cloneMetaKiVar :: TcKiVar -> TcM TcKiVar
cloneMetaKiVar kv = assert (isTcKiVar kv) $ do
  ref <- newMutVar Flexi
  name' <- cloneMetaKiVarName (kiVarName kv)
  let details' = case tcKiVarDetails kv of
                   details@(MetaKv {}) -> details { mkv_ref = ref }
                   _ -> pprPanic "cloneMetaKiVar" (ppr kv)
      kivar = mkTcKiVar name' details'
  traceTc "cloneMetaKiVar" (ppr kivar)
  return kivar

cloneMetaKiVarWithInfo :: MetaInfoK -> TcLevel -> TcKiVar -> TcM TcKiVar
cloneMetaKiVarWithInfo info tc_lvl kv = assert (isTcKiVar kv) $ do
  ref <- newMutVar Flexi
  name' <- cloneMetaKiVarName (kiVarName kv)
  let details = MetaKv { mkv_info = info
                       , mkv_ref = ref
                       , mkv_tclvl = tc_lvl }
      kivar = mkTcKiVar name' details
  traceTc "cloneMetaKiVarWithInfo" (ppr kivar)
  return kivar

readMetaTyVar :: MonadIO m => TypeVar -> m MetaDetails
readMetaTyVar tyvar = assertPpr (isMetaTyVar tyvar) (ppr tyvar)
  $ liftIO $ readIORef (metaTyVarRef tyvar)
{-# SPECIALIZE readMetaTyVar :: TypeVar -> TcM MetaDetails #-}
{-# SPECIALIZE readMetaTyVar :: TypeVar -> ZonkM MetaDetails #-}

readMetaKiVar :: MonadIO m => KindVar -> m MetaDetailsK
readMetaKiVar kivar = assertPpr (isMetaKiVar kivar) (ppr kivar)
  $ liftIO $ readIORef (metaKiVarRef kivar)
{-# SPECIALIZE readMetaKiVar :: KindVar -> TcM MetaDetailsK #-}
{-# SPECIALIZE readMetaKiVar :: KindVar -> ZonkM MetaDetailsK #-}

isFilledMetaKiVar_maybe :: TcKiVar -> TcM (Maybe Kind)
isFilledMetaKiVar_maybe kv
  | isTcKiVar kv
  , MetaKv { mkv_ref = ref } <- tcKiVarDetails kv
  = do cts <- readTcRef ref
       case cts of
         Indirect ki -> return $ Just ki
         Flexi -> return Nothing
  | otherwise
  = return Nothing

{- *********************************************************************
*                                                                      *
        MetaKvs: TauKvs
*                                                                      *
********************************************************************* -}

newOpenTypeKind :: TcM TcKind
newOpenTypeKind = newFlexiKiVarKi

newFlexiKiVar :: TcM TcKiVar
newFlexiKiVar = newAnonMetaKiVar TauKv

newFlexiKiVarKi :: TcM TcKind
newFlexiKiVarKi = do
  tc_kivar <- newFlexiKiVar
  return $ mkKiVarKi tc_kivar

{- *********************************************************************
*                                                                      *
             Finding variables to quantify over
*                                                                      *
********************************************************************* -}

candidateQKiVarsOfKind :: TcKind -> TcM DKiVarSet
candidateQKiVarsOfKind ki = do
  cur_lvl <- getTcLevel
  collect_cand_qkvs ki cur_lvl emptyVarSet emptyDVarSet ki

collect_cand_qkvs
  :: TcKind
  -> TcLevel
  -> VarSet
  -> DKiVarSet
  -> Kind
  -> TcM DKiVarSet
collect_cand_qkvs orig_ki cur_lvl bound dvs ki = go dvs ki
  where
    is_bound kv = kv `elemVarSet` bound

    -----------------
    go :: DKiVarSet -> TcKind -> TcM DKiVarSet
    go dv (KiCon _) = return dv
    go dv (KiVarKi kv)
      | is_bound kv = return dv
      | otherwise = do
          m_contents <- isFilledMetaKiVar_maybe kv
          case m_contents of
            Just ind_ki -> go dv ind_ki
            Nothing -> go_kv dv kv
    go dv (FunKd _ k1 k2) = foldM go dv [k1, k2]
    go dv (KdContext rels) = foldM go_rel dv rels

    go_rel dv (LTKd k1 k2) = foldM go dv [k1, k2]
    go_rel dv (LTEQKd k1 k2) = foldM go dv [k1, k2]

    go_kv dv kv
      | tcKiVarLevel kv <= cur_lvl
      = return dv
      | kv `elemDVarSet` dv
      = return dv
      | otherwise
      = return $ dv `extendDVarSet` kv

{- *********************************************************************
*                                                                      *
             Quantification
*                                                                      *
********************************************************************* -}

quantifyKiVars :: SkolemInfo -> DKiVarSet -> TcM [TcKiVar]
quantifyKiVars skol_info kvs
  | isEmptyDVarSet kvs
  = do traceTc "quantifyKiVars has nothing to quantify" empty
       return []
  | otherwise
  = do traceTc "quantifyKiVars {"
         $ vcat [ text "kvs =" <+> ppr kvs ]

       final_qkvs <- liftZonkM $ mapMaybeM zonk_quant (dVarSetElems kvs)

       traceTc "quantifyKiVars }"
         $ vcat [ text "final_qkvs =" <+> (sep $ map ppr final_qkvs) ]

       return final_qkvs
  where
    zonk_quant kv
      | not (isKiVar kv) = return Nothing
      | otherwise = Just <$> skolemizeQuantifiedKiVar skol_info kv

zonkAndSkolemize :: SkolemInfo -> TcVar -> ZonkM TcTyVar
zonkAndSkolemize skol_info var
  | isTyVarTyVar var
  = do zonked_tyvar <- zonkTcTyVarToTcTyVar var
       skolemizeQuantifiedTyVar skol_info zonked_tyvar
  | isKiVarKiVar var
  = do zonked_kivar <- zonkTcKiVarToTcKiVar var
       skolemizeQuantifiedKiVar skol_info zonked_kivar
  | otherwise
  = assertPpr (isImmutableTyVar var) (pprTyVar var)
    $ zonkTyVarKind var

skolemizeQuantifiedTyVar :: SkolemInfo -> TcTyVar -> ZonkM TcTyVar
skolemizeQuantifiedTyVar skol_info tv
  = case tcTyVarDetails tv of
      MetaTv {} -> skolemizeUnboundMetaTyVar skol_info tv
      SkolemTv _ lvl -> do kind <- zonkTcKind (tyVarKind tv)
                           let details = SkolemTv skol_info lvl
                               name = tyVarName tv
                           return $ mkTcTyVar name kind details

skolemizeQuantifiedKiVar :: SkolemInfo -> TcKiVar -> ZonkM TcKiVar
skolemizeQuantifiedKiVar skol_info kv
  = case tcKiVarDetails kv of
      MetaKv {} -> skolemizeUnboundMetaKiVar skol_info kv
      SkolemKv _ lvl -> do let details = SkolemKv skol_info lvl
                               name = kiVarName kv
                           return $ mkTcKiVar name details

skolemizeUnboundMetaTyVar :: SkolemInfo -> TcTyVar -> ZonkM TypeVar
skolemizeUnboundMetaTyVar skol_info tv = assertPpr (isMetaTyVar tv) (ppr tv) $ do
  check_empty tv
  ZonkGblEnv { zge_src_span = here, zge_tc_level = tc_lvl } <- getZonkGblEnv
  kind <- zonkTcKind (tyVarKind tv)
  let tv_name = tyVarName tv
      final_name | isSystemName tv_name
                 = mkInternalName (nameUnique tv_name) (nameOccName tv_name) here
                 | otherwise
                 = tv_name
      details = SkolemTv skol_info (pushTcLevel tc_lvl)
      final_tv = mkTcTyVar final_name kind details

  traceZonk "Skolemizing" (ppr tv <+> text ":=" <+> ppr final_tv)
  writeMetaTyVar tv (mkTyVarTy final_tv)
  return final_tv
  where
    check_empty tv = when debugIsOn $ do
      cts <- readMetaTyVar tv
      case cts of
        Flexi -> return ()
        Indirect ty -> warnPprTrace True "skolemizeUnboundMetaTyVar" (ppr tv $$ ppr ty)
                       $ return ()
                   
skolemizeUnboundMetaKiVar :: SkolemInfo -> TcKiVar -> ZonkM KindVar
skolemizeUnboundMetaKiVar skol_info kv = assertPpr (isMetaKiVar kv) (ppr kv) $ do
  check_empty kv
  ZonkGblEnv { zge_src_span = here, zge_tc_level = tc_lvl } <- getZonkGblEnv
  let kv_name = kiVarName kv
      final_name | isSystemName kv_name
                 = mkInternalName (nameUnique kv_name) (nameOccName kv_name) here
                 | otherwise
                 = kv_name
      details = SkolemKv skol_info (pushTcLevel tc_lvl)
      final_kv = mkTcKiVar final_name details

  traceZonk "Skolemizing" (ppr kv <+> text ":=" <+> ppr final_kv)
  writeMetaKiVar kv (mkKiVarKi final_kv)
  return final_kv
  where
    check_empty kv = when debugIsOn $ do
      cts <- readMetaKiVar kv
      case cts of
        Flexi -> return ()
        Indirect ki -> warnPprTrace True "skolemizeUnboundMetaKiVar" (ppr kv $$ ppr ki)
                       $ return ()

{- *********************************************************************
*                                                                      *
              Promotion
*                                                                      *
********************************************************************* -}

promoteMetaKiVarTo :: HasDebugCallStack => TcLevel -> TcKiVar -> TcM Bool
promoteMetaKiVarTo tclvl kv
  | assertPpr (isMetaKiVar kv) (ppr kv)
    $ tcKiVarLevel kv `strictlyDeeperThan` tclvl
  = do cloned_kv <- cloneMetaKiVar kv
       let rhs_kv = setMetaKiVarTcLevel cloned_kv tclvl
       liftZonkM $ writeMetaKiVar kv (mkKiVarKi rhs_kv)
       traceTc "promoteKiVar" (ppr kv <+> text "-->" <+> ppr rhs_kv)
       return True
  | otherwise
  = return False

promoteKiVarSet :: HasDebugCallStack => KiVarSet -> TcM Bool
promoteKiVarSet kvs = do
  tclvl <- getTcLevel
  bools <- mapM (promoteMetaKiVarTo tclvl)
           $ filter isPromotableMetaKiVar
           $ nonDetEltsUniqSet kvs
  return $ or bools
