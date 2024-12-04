module CSlash.Tc.Utils.TcMType where

import CSlash.Cs
import CSlash.Platform

import CSlash.Driver.DynFlags

-- import {-# SOURCE #-} GHC.Tc.Utils.Unify( unifyInvisibleType, tcSubMult )
import CSlash.Tc.Types.Origin
-- import GHC.Tc.Types.Constraint
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
        MetaKvs
*                                                                      *
********************************************************************* -}

newMetaKiVarName :: FastString -> TcM Name
newMetaKiVarName str = newSysName (mkKiVarOccFS str)

cloneMetaKiVarName :: Name -> TcM Name
cloneMetaKiVarName name = newSysName (nameOccName name)

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
    go dv UKd = return dv
    go dv AKd = return dv
    go dv LKd = return dv
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


zonkAndSkolemize :: SkolemInfo -> TcTyVar -> ZonkM TcTyVar
zonkAndSkolemize skol_info tyvar = panic "zonkAndSkolemize"

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
