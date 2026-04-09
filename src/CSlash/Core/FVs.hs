{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

module CSlash.Core.FVs where

import CSlash.Cs.Pass

import CSlash.Core as Core
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.Name.Set
import CSlash.Types.Name hiding (varName)
import CSlash.Types.Tickish
import CSlash.Types.Basic
import CSlash.Types.Var.Set
import CSlash.Types.Var
import CSlash.Core.Type
import CSlash.Core.Type.Rep hiding (E3(..))
import qualified CSlash.Core.Type.Rep as TFV
import CSlash.Core.Type.FVs
import CSlash.Core.Kind
import CSlash.Core.Kind.FVs
import CSlash.Core.TyCon
-- import CSlash.Builtin.Types( unrestrictedFunTyConName )
import CSlash.Builtin.Types.Prim( fUNTyCon )
import CSlash.Data.Maybe( orElse )

import CSlash.Utils.FV as FV
import CSlash.Utils.Misc
import CSlash.Utils.Panic.Plain

import Data.List (unzip5)

{- *********************************************************************
*                                                                      *
         Finding the free variables of an expression
*                                                                      *
********************************************************************* -}

data E5 a b c d e = In1 a | In2 b | In3 c | In4 d | In5 e

instance HasFVs CoreExpr where
  type FVInScope CoreExpr = (IdSet Zk, TyCoVarSet Zk, TyVarSet Zk, KiCoVarSet Zk, KiVarSet Zk)
  type FVAcc CoreExpr = ( [Id Zk], IdSet Zk
                        , [TyCoVar Zk], TyCoVarSet Zk
                        , [TyVar Zk], TyVarSet Zk
                        , [KiCoVar Zk], KiCoVarSet Zk
                        , [KiVar Zk], KiVarSet Zk )
  type FVArg CoreExpr = E5 (Id Zk) (TyCoVar Zk) (TyVar Zk) (KiCoVar Zk) (KiVar Zk)

  fvElemAcc (In1 id) (_, haveSet, _, _, _, _, _, _, _, _) = id `elemVarSet` haveSet
  fvElemAcc (In2 tcv) (_, _, _, haveSet, _, _, _, _, _, _) = tcv `elemVarSet` haveSet
  fvElemAcc (In3 tv) (_, _, _, _, _, haveSet, _, _, _, _) = tv `elemVarSet` haveSet
  fvElemAcc (In4 kcv) (_, _, _, _, _, _, _, haveSet, _, _) = kcv `elemVarSet` haveSet
  fvElemAcc (In5 kv) (_, _, _, _, _, _, _, _, _, haveSet) = kv `elemVarSet` haveSet

  fvElemIS (In1 id) (in_scope, _, _, _, _) = id `elemVarSet` in_scope
  fvElemIS (In2 tcv) (_, in_scope, _, _, _) = tcv `elemVarSet` in_scope
  fvElemIS (In3 tv) (_, _, in_scope, _, _) = tv `elemVarSet` in_scope
  fvElemIS (In4 kcv) (_, _, _, in_scope, _) = kcv `elemVarSet` in_scope
  fvElemIS (In5 kv) (_, _, _, _, in_scope) = kv `elemVarSet` in_scope

  fvExtendAcc (In1 id) (have, haveSet, tcs, tcset, tvs, tvset, kcs, kcset, ks, kset)
    = (id:have, extendVarSet haveSet id, tcs, tcset, tvs, tvset, kcs, kcset, ks, kset)
  fvExtendAcc (In2 tcv) (ids, idset, have, haveSet, tvs, tvset, kcs, kcset, ks, kset)
    = (ids, idset, tcv:have, extendVarSet haveSet tcv, tvs, tvset, kcs, kcset, ks, kset)
  fvExtendAcc (In3 tv) (ids, idset, tcs, tcset, have, haveSet, kcs, kcset, ks, kset)
    = (ids, idset, tcs, tcset, tv:have, extendVarSet haveSet tv, kcs, kcset, ks, kset)
  fvExtendAcc (In4 kcv) (ids, idset, tcs, tcset, ts, tset, have, haveSet, ks, kset)
    = (ids, idset, tcs, tcset, ts, tset, kcv:have, extendVarSet haveSet kcv, ks, kset)
  fvExtendAcc (In5 kv) (ids, idset, tcs, tcset, ts, tset, kcs, kcset, have, haveSet)
    = (ids, idset, tcs, tcset, ts, tset, kcs, kcset, kv:have, extendVarSet haveSet kv)

  fvExtendIS (In1 id) (in_scope, tcs, ts, kcs, ks)
    = (extendVarSet in_scope id, tcs, ts, kcs, ks)
  fvExtendIS (In2 tcv) (ids, in_scope, ts, kcs, ks)
    = (ids, extendVarSet in_scope tcv, ts, kcs, ks)
  fvExtendIS (In3 tv) (ids, tcs, in_scope, kcs, ks)
    = (ids, tcs, extendVarSet in_scope tv, kcs, ks)
  fvExtendIS (In4 kcv) (ids, tcs, ts, in_scope, ks)
    = (ids, tcs, ts, extendVarSet in_scope kcv, ks)
  fvExtendIS (In5 kv) (ids, tcs, ts, kcs, in_scope)
    = (ids, tcs, ts, kcs, extendVarSet in_scope kv)

  fvEmptyAcc = ( [], emptyVarSet
               , [], emptyVarSet
               , [], emptyVarSet
               , [], emptyVarSet
               , [], emptyVarSet)
  fvEmptyIS = (emptyVarSet, emptyVarSet, emptyVarSet, emptyVarSet, emptyVarSet)
  
type CoreFV = FV (CoreExpr)

liftKiToCoreFV :: KiFV Zk -> CoreFV
liftKiToCoreFV kfv f (_, _, _, _, kis)
               (idaccl, idaccs, tcaccl, tcaccs, taccl, taccs, kcaccl, kcaccs, kaccl, kaccs)
  = case kfv (f . In5) kis (kaccl, kaccs) of
      (kaccl, kaccs) -> ( idaccl, idaccs
                        , tcaccl, tcaccs
                        , taccl, taccs
                        , kcaccl, kcaccs
                        , kaccl, kaccs )
 
liftTyToCoreFV :: TyFV Zk -> CoreFV
liftTyToCoreFV tfv f (_, _, tis, kcis, kis)
               (idaccl, idaccs, tcaccl, tcaccs, taccl, taccs, kcaccl, kcaccs, kaccl, kaccs)
  = case tfv new_f (tis, kcis, kis) (taccl, taccs, kcaccl, kcaccs, kaccl, kaccs) of
      (taccl, taccs, kcaccl, kcaccs, kaccl, kaccs)
        -> (idaccl, idaccs, tcaccl, tcaccs, taccl, taccs, kcaccl, kcaccs, kaccl, kaccs)
  where
    new_f (TFV.In1 v) = f (In3 v)
    new_f (TFV.In2 v) = f (In4 v)
    new_f (TFV.In3 v) = f (In5 v)

exprFreeVars :: CoreExpr -> (IdSet Zk, TyCoVarSet Zk, TyVarSet Zk, KiCoVarSet Zk, KiVarSet Zk)
exprFreeVars e = case fvVarAcc (exprLocalFVs e) of
  (_, ids, _, tcs, _, ts, _, kcs, _, ks) -> (ids, tcs, ts, kcs, ks)

exprLocalFVs :: CoreExpr -> CoreFV
exprLocalFVs = filterFV isLocal . exprFVs
  where isLocal (In1 id) = isLocalId id
        isLocal _ = True

addLetBndrFV :: CoreId -> CoreFV -> CoreFV
addLetBndrFV id fv fv_cand in_scope acc =
  (liftTyToCoreFV (fvsOfType (varType id)) `unionFV`
   FV.delFV (In1 id) fv) fv_cand in_scope acc

addLamBndrFV :: CoreBndr -> CoreFV -> CoreFV
addLamBndrFV bndr fv fv_cand in_scope acc = case bndr of
  Core.Id id ->
    (liftTyToCoreFV (fvsOfType (varType id)) `unionFV`
     FV.delFV (In1 id) fv) fv_cand in_scope acc
  Tv tv ->
    (liftKiToCoreFV (fvsOfMonoKind (varKind tv)) `unionFV`
     FV.delFV (In3 tv) fv) fv_cand in_scope acc
  KCv kcv ->
    (liftKiToCoreFV (fvsOfMonoKind (varKind kcv)) `unionFV`
     FV.delFV (In4 kcv) fv) fv_cand in_scope acc
  Kv kv ->
    (FV.delFV (In5 kv) fv) fv_cand in_scope acc

addLetBndrsFV :: [CoreId] -> CoreFV -> CoreFV
addLetBndrsFV bndrs fv = foldr addLetBndrFV fv bndrs

addLamBndrsFV :: [CoreBndr] -> CoreFV -> CoreFV
addLamBndrsFV bndrs fv = foldr addLamBndrFV fv bndrs

exprsFVs :: [CoreExpr] -> CoreFV
exprsFVs exprs = mapUnionFV exprFVs exprs

exprFVs :: CoreExpr -> CoreFV
exprFVs (Type ty) fv_cand in_scope acc = liftTyToCoreFV (fvsOfType ty) fv_cand in_scope acc
exprFVs (KiCo co) fv_cand in_scope acc = liftTyToCoreFV (fvsOfKiCo co) fv_cand in_scope acc
exprFVs (Kind ki) fv_cand in_scope acc = liftKiToCoreFV (fvsOfMonoKind ki) fv_cand in_scope acc
exprFVs (Var var) fv_cand in_scope acc = FV.unitFV (In1 var) fv_cand in_scope acc
exprFVs (Lit _) fv_cand in_scope acc = emptyFV fv_cand in_scope acc
exprFVs (Tick _ expr) fv_cand in_scope acc = exprFVs expr fv_cand in_scope acc
exprFVs (App fun arg) fv_cand in_scope acc
  = (exprFVs fun `unionFV` exprFVs arg) fv_cand in_scope acc
exprFVs (Lam bndr Nothing body) fv_cand in_scope acc
  = addLamBndrFV bndr (exprFVs body) fv_cand in_scope acc
exprFVs (Lam bndr (Just ki) body) fv_cand in_scope acc
  = (liftKiToCoreFV (fvsOfMonoKind ki) `unionFV`
     addLamBndrFV bndr (exprFVs body)) fv_cand in_scope acc
exprFVs (Cast expr co) fv_cand in_scope acc
  = (exprFVs expr `unionFV` fvsOfTyCo co) fv_cand in_scope acc
exprFVs (Case scrut bndr ty alts) fv_cand in_scope acc
  = (exprFVs scrut `unionFV` liftTyToCoreFV (fvsOfType ty) `unionFV` addLetBndrFV bndr
     (mapUnionFV alt_fvs alts)) fv_cand in_scope acc
  where
    alt_fvs (Alt _ bndrs rhs) = addLetBndrsFV bndrs (exprFVs rhs)
exprFVs (Let (NonRec bndr rhs) body) fv_cand in_scope acc
  = (rhs_fvs (bndr, rhs) `unionFV` addLetBndrFV bndr (exprFVs body)) fv_cand in_scope acc
exprFVs (Let (Rec pairs) body) fv_cand in_scope acc
  = addLetBndrsFV (map fst pairs)
    (mapUnionFV rhs_fvs pairs `unionFV` exprFVs body)
    fv_cand in_scope acc

rhs_fvs :: (CoreId, CoreExpr) -> CoreFV
rhs_fvs (bndr, rhs) = exprFVs rhs `unionFV` idUnfoldingFVs bndr

fvsOfTyCos :: [TypeCoercion Zk] -> CoreFV
fvsOfTyCos [] fv_cand in_scope acc = emptyFV fv_cand in_scope acc
fvsOfTyCos (co:cos) fv_cand in_scope acc
  = (fvsOfTyCo co `unionFV` fvsOfTyCos cos) fv_cand in_scope acc

-- Here because it returns a CoreFV (could be moved but would result in some duplication)
-- This is also simplet since it just has 'Zk', not a generic pass.
fvsOfTyCo :: TypeCoercion Zk -> CoreFV
fvsOfTyCo (TyRefl ty) fv_cand in_scope acc
  = liftTyToCoreFV (fvsOfType ty) fv_cand in_scope acc
fvsOfTyCo (GRefl ty kco) fv_cand in_scope acc
  = (liftTyToCoreFV (fvsOfType ty) `unionFV` liftTyToCoreFV (fvsOfKiCo kco))
    fv_cand in_scope acc
fvsOfTyCo (TyConAppCo _ cos) fv_cand in_scope acc
  = fvsOfTyCos cos fv_cand in_scope acc
fvsOfTyCo (AppCo co arg) fv_cand in_scope acc
  = (fvsOfTyCo co `unionFV` fvsOfTyCo arg) fv_cand in_scope acc
fvsOfTyCo (ForAllCo { tfco_tv = tv, tfco_tv_kind_co = kco, tfco_body = co }) fv_cand in_scope acc
  = (addLamBndrFV (Tv tv) (fvsOfTyCo co) `unionFV` liftTyToCoreFV (fvsOfKiCo kco))
    fv_cand in_scope acc
fvsOfTyCo (ForAllCoCo { tfcoco_kcv = kcv, tfcoco_kcv_kind_co = kco, tfcoco_body = co })
          fv_cand in_scope acc
  = (addLamBndrFV (KCv kcv) (fvsOfTyCo co) `unionFV` liftTyToCoreFV (fvsOfKiCo kco))
    fv_cand in_scope acc
fvsOfTyCo (TyFunCo { tfco_ki = kco, tfco_arg = co1, tfco_res = co2 }) fv_cand in_scope acc
  = (fvsOfTyCo co1 `unionFV` fvsOfTyCo co2 `unionFV` liftTyToCoreFV (fvsOfKiCo kco))
    fv_cand in_scope acc
fvsOfTyCo (TyCoVarCo v) fv_cand in_scope acc
  = fvsOfTyCoVar v fv_cand in_scope acc
fvsOfTyCo (LiftKCo kco) fv_cand in_scope acc
  = liftTyToCoreFV (fvsOfKiCo kco) fv_cand in_scope acc
fvsOfTyCo (TySymCo co) fv_cand in_scope acc = fvsOfTyCo co fv_cand in_scope acc
fvsOfTyCo (TyTransCo co1 co2) fv_cand in_scope acc
  = (fvsOfTyCo co1 `unionFV` fvsOfTyCo co2) fv_cand in_scope acc
fvsOfTyCo (LRCo _ co) fv_cand in_scope acc = fvsOfTyCo co fv_cand in_scope acc

fvsOfTyCoVar :: TyCoVar Zk -> CoreFV
fvsOfTyCoVar v fv_cand in_scope acc
  = (FV.unitFV (In2 v) `unionFV` liftTyToCoreFV (fvsOfType (varType v))) fv_cand in_scope acc

{- *********************************************************************
*                                                                      *
            Attaching free variables to every sub-expression
*                                                                      *
********************************************************************* -}

type DCoreIdSet = DIdSet Zk
type DCoreTyCoVarSet = DTyCoVarSet Zk
type DCoreTyVarSet = DTyVarSet Zk
type DCoreKiCoVarSet = DKiCoVarSet Zk
type DCoreKiVarSet = DKiVarSet Zk

type FVAnn = (DCoreIdSet, DCoreTyCoVarSet, DCoreTyVarSet, DCoreKiCoVarSet, DCoreKiVarSet)

type CoreBindWithFVs = AnnBind CoreBndr CoreId FVAnn

type CoreExprWithFVs = AnnExpr CoreBndr CoreId FVAnn

type CoreAltWithFVs = AnnAlt CoreBndr CoreId FVAnn

freeVarsOf :: CoreExprWithFVs -> FVAnn
freeVarsOf (fvs, _) = fvs

aFreeId :: CoreId -> FVAnn
aFreeId id = (unitDVarSet id, emptyDVarSet, emptyDVarSet, emptyDVarSet, emptyDVarSet)

emptyFVAnn :: FVAnn
emptyFVAnn = (emptyDVarSet, emptyDVarSet, emptyDVarSet, emptyDVarSet, emptyDVarSet)

unionFVs :: FVAnn -> FVAnn -> FVAnn
unionFVs (id1, tcv1, tv1, kcv1, kv1) (id2, tcv2, tv2, kcv2, kv2)
  = ( unionDVarSet id1 id2
    , unionDVarSet tcv1 tcv2
    , unionDVarSet tv1 tv2
    , unionDVarSet kcv1 kcv2
    , unionDVarSet kv1 kv2 )

unionFVss :: [FVAnn] -> FVAnn
unionFVss fvs
  = let (ids, tcvs, tvs, kcvs, kvs) = unzip5 fvs
    in ( unionDVarSets ids
       , unionDVarSets tcvs
       , unionDVarSets tvs
       , unionDVarSets kcvs
       , unionDVarSets kvs )

delLamBindersFV :: [CoreBndr] -> FVAnn -> FVAnn
delLamBindersFV bs fvs = foldr delLamBinderFV fvs bs

delLamBinderFV :: CoreBndr -> FVAnn -> FVAnn
delLamBinderFV (Core.Id id) s = delLetBinderFV id s
delLamBinderFV (Tv tv) (ids, tcvs, tvs, kcvs, kvs)
  = (ids, tcvs, tvs `delDVarSet` tv, kcvs, kvs)
    `unionFVs` dTyVarFVs tv
delLamBinderFV (KCv kcv) (ids, tcvs, tvs, kcvs, kvs)
  = (ids, tcvs, tvs, kcvs `delDVarSet` kcv, kvs)
    `unionFVs` dKiCoVarFVs kcv
delLamBinderFV (Kv kv) (ids, tcvs, tvs, kcvs, kvs)
  = (ids, tcvs, tvs, kcvs, kvs `delDVarSet` kv)

delLetBindersFV :: [CoreId] -> FVAnn -> FVAnn
delLetBindersFV bs fvs = foldr delLetBinderFV fvs bs

delLetBinderFV :: CoreId -> FVAnn -> FVAnn
delLetBinderFV id (ids, tcvs, tvs, kcvs, kvs)
  = (ids `delDVarSet` id, tcvs, tvs, kcvs, kvs)
    `unionFVs` dIdFVs id

dIdFreeVars :: CoreId -> FVAnn
dIdFreeVars id = fvDVarSets $ liftTyToCoreFV (fvsOfType (varType id)) `unionFV` idUnfoldingFVs id  

fvDVarSets :: CoreFV -> FVAnn
fvDVarSets fvs = case fvVarAcc fvs of
  (ids, _, tcvs, _, tvs, _, kcvs, _, kvs, _)
    -> (mkDVarSet ids, mkDVarSet tcvs, mkDVarSet tvs, mkDVarSet kcvs, mkDVarSet kvs)

fvVarSets
  :: CoreFV
  -> (IdSet Zk, TyCoVarSet Zk, TyVarSet Zk, KiCoVarSet Zk, KiVarSet Zk)
fvVarSets fvs = case fvVarAcc fvs of
  (_, ids, _, tcvs, _, tvs, _, kcvs, _, kvs)
    -> (ids, tcvs, tvs, kcvs, kvs)

fvAccDVarSets :: FVAcc CoreExpr -> FVAnn
fvAccDVarSets (ids, _, tcvs, _, tvs, _, kcvs, _, kvs, _)
  = (mkDVarSet ids, mkDVarSet tcvs, mkDVarSet tvs, mkDVarSet kcvs, mkDVarSet kvs)

dIdFVs :: CoreId -> FVAnn
dIdFVs id = fvDVarSets $ liftTyToCoreFV (fvsOfType (varType id))

dTyVarFVs :: CoreTyVar -> FVAnn
dTyVarFVs tv = fvDVarSets $ liftKiToCoreFV (fvsOfMonoKind (varKind tv))

dKiCoVarFVs :: CoreKiCoVar -> FVAnn
dKiCoVarFVs kcv = fvDVarSets $ liftKiToCoreFV (fvsOfMonoKind (varKind kcv))

bndrRuleAndUnfoldingVarsDSet :: CoreId -> FVAnn
bndrRuleAndUnfoldingVarsDSet id = fvDVarSets $ bndrRuleAndUnfoldingFVs id

bndrRuleAndUnfoldingFVs :: CoreId -> CoreFV
bndrRuleAndUnfoldingFVs id = idRuleFVs id `unionFV` idUnfoldingFVs id

idRuleFVs :: CoreId -> CoreFV
idRuleFVs id
  = let (ids, tcvs, tvs, kcvs, kvs) = ruleInfoFreeVars (idSpecialization id)
        ids' = In1 <$> dVarSetElems ids
        tcvs' = In2 <$> dVarSetElems tcvs
        tvs' = In3 <$> dVarSetElems tvs
        kcvs' = In4 <$> dVarSetElems kcvs
        kvs' = In5 <$> dVarSetElems kvs
    in FV.mkFVs (ids' ++ tcvs' ++ tvs' ++ kcvs' ++ kvs')

idUnfoldingFVs :: CoreId -> CoreFV
idUnfoldingFVs id = stableUnfoldingFVs (realIdUnfolding id) `orElse` emptyFV

bndrRuleAndUnfoldingIds :: CoreId -> IdSet Zk
bndrRuleAndUnfoldingIds id = case fvVarSets $ bndrRuleAndUnfoldingFVs id of
  (ids, _, _, _, _) -> ids

stableUnfoldingFVs :: Unfolding -> Maybe CoreFV
stableUnfoldingFVs unf
  = case unf of
      CoreUnfolding { uf_tmpl = rhs, uf_src = src }
        | isStableSource src
        -> Just (exprLocalFVs rhs)
      _ -> Nothing

{- *********************************************************************
*                                                                      *
            Free variables
*                                                                      *
********************************************************************* -}

freeVarsBind
  :: CoreBind
  -> FVAnn
  -> (CoreBindWithFVs, FVAnn)
freeVarsBind (NonRec binder rhs) body_fvs
  = ( AnnNonRec binder rhs2
    , freeVarsOf rhs2
      `unionFVs` body_fvs2
      `unionFVs` bndrRuleAndUnfoldingVarsDSet binder )
  where
    rhs2 = freeVars rhs
    body_fvs2 = binder `delLetBinderFV` body_fvs
    
freeVarsBind (Rec binds) body_fvs
  = ( AnnRec (binders `zip` rhss2)
    , delLetBindersFV binders all_fvs )
  where
    (binders, rhss) = unzip binds
    rhss2 = map freeVars rhss
    rhs_body_fvs = foldr (unionFVs . freeVarsOf) body_fvs rhss2
    binders_fvs = fvDVarSets $ mapUnionFV idUnfoldingFVs binders
    all_fvs = rhs_body_fvs `unionFVs` binders_fvs
    
freeVars :: CoreExpr -> CoreExprWithFVs
freeVars = go
  where
    go :: CoreExpr -> CoreExprWithFVs
    go (Var v)
      | isLocalId v = (aFreeId v `unionFVs` ty_fvs, AnnVar v)
      | otherwise = (emptyFVAnn, AnnVar v)
      where ty_fvs = dIdFVs v
    go (Lit lit) = (emptyFVAnn, AnnLit lit)
    go (Lam b k body)
      = ( b_fvs `unionFVs` k_fvs `unionFVs` (b `delLamBinderFV` body_fvs)
        , AnnLam b k' body' )
      where
        body'@(body_fvs, _) = go body
        b_fvs = case b of -- TODO: this is redundant since we call 'delLamBinderFV', right??
                  Core.Id id -> dIdFVs id
                  Tv tv -> dTyVarFVs tv
                  KCv kcv -> dKiCoVarFVs kcv
                  Kv _ -> emptyFVAnn
        (k', k_fvs) = case k of
          Just ki -> let fvs = fvDVarSets $ liftKiToCoreFV $ fvsOfMonoKind ki
                     in (Just (fvs, ki), fvs)
          Nothing -> (Nothing, emptyFVAnn)
    go (App fun arg)
      = ( freeVarsOf fun' `unionFVs` freeVarsOf arg'
        , AnnApp fun' arg' )
      where
        fun' = go fun
        arg' = go arg
    go (Case scrut bndr ty alts)
      = ( (bndr `delLetBinderFV` alts_fvs)
          `unionFVs` freeVarsOf scrut2
          `unionFVs` (fvDVarSets $ liftTyToCoreFV $ fvsOfType ty)
        , AnnCase scrut2 bndr ty alts2 )
      where
        scrut2 = go scrut

        (alts_fvs_s, alts2) = mapAndUnzip fv_alt alts
        alts_fvs = unionFVss alts_fvs_s

        fv_alt (Alt con args rhs) = ( delLetBindersFV args (freeVarsOf rhs2)
                                    , (AnnAlt con args rhs2) )
          where rhs2 = go rhs
    go (Let bind body)
      = (bind_fvs, AnnLet bind2 body2)
      where
        (bind2, bind_fvs) = freeVarsBind bind (freeVarsOf body2)
        body2 = go body
    go (Cast expr co)
      = ( freeVarsOf expr2 `unionFVs` cfvs
        , AnnCast expr2 (cfvs, co) )
      where
        expr2 = go expr
        cfvs = fvDVarSets $ fvsOfTyCo co
    go (Tick tickish expr)
      = panic "Tick fvs"
    go (Type ty) = (fvDVarSets $ liftTyToCoreFV $ fvsOfType ty, AnnType ty)
    go (KiCo co) = (fvDVarSets $ liftTyToCoreFV $ fvsOfKiCo co, AnnKiCo co)
    go (Kind ki) = (fvDVarSets $ liftKiToCoreFV $ fvsOfMonoKind ki, AnnKind ki)

{- **********************************************************************
*                                                                       *
                    Orphan names
*                                                                       *
%********************************************************************* -}

orphNamesOfTyCon :: TyCon Zk -> NameSet
orphNamesOfTyCon tycon = unitNameSet (getName tycon)

orphNamesOfType :: CoreType -> NameSet
orphNamesOfType ty | Just ty' <- coreView ty = orphNamesOfType ty'
orphNamesOfType (TyVarTy _) = emptyNameSet
orphNamesOfType (ForAllTy _ res) = orphNamesOfType res
orphNamesOfType (ForAllKiCo _ res) = orphNamesOfType res
orphNamesOfType (AppTy fun arg) = orphNamesOfType fun `unionNameSet` orphNamesOfType arg
orphNamesOfType (TyConApp tycon tys) = orphNamesOfTyCon tycon
                                       `unionNameSet` orphNamesOfTypes tys
orphNamesOfType (FunTy _ arg res) = unitNameSet (tyConName fUNTyCon)
                                    `unionNameSet` orphNamesOfType arg
                                    `unionNameSet` orphNamesOfType res
orphNamesOfType (CastTy ty _) = orphNamesOfType ty
orphNamesOfType (KindCoercion _) = emptyNameSet
orphNamesOfType BigTyLamTy{} = panic "orphNamesOfType BigTyLamTy" -- TODO: maybe not a panic
orphNamesOfType TyLamTy{} = panic "orphNamesOfType TyLamTy"
orphNamesOfType Embed{} = emptyNameSet

orphNamesOfTypes :: [CoreType] -> NameSet
orphNamesOfTypes = foldr (unionNameSet . orphNamesOfType) emptyNameSet

orphNamesOfExpr :: CoreExpr -> NameSet
orphNamesOfExpr e = go e
  where
    go (Var v)
      | isExternalName n = unitNameSet n
      | otherwise = emptyNameSet
      where n = varName v
    go (Lit _) = emptyNameSet
    go (Type ty) = orphNamesOfType ty
    go (KiCo _) = emptyNameSet
    go (Kind _) = emptyNameSet
    go (App e1 e2) = go e1 `unionNameSet` go e2
    go (Lam v _ e) = go e `delFromNameSet` bndrName v
    go (Tick _ e) = go e
    go (Cast e _) = go e
    go (Let (NonRec _ r) e) = go e `unionNameSet` go r
    go (Let (Rec prs) e) = orphNamesOfExprs (map snd prs) `unionNameSet` go e
    go (Case e _ ty as) = go e `unionNameSet` orphNamesOfType ty
                               `unionNameSet` unionNameSets (map go_alt as)

    go_alt (Alt _ _ r) = go r

orphNamesOfExprs :: [CoreExpr] -> NameSet
orphNamesOfExprs es = foldr (unionNameSet . orphNamesOfExpr) emptyNameSet es

{- *********************************************************************
*                                                                      *
                        Rules
*                                                                      *
********************************************************************* -}

data RuleFVsFrom
  = LhsOnly
  | RhsOnly
  | BothSides

ruleFVs :: RuleFVsFrom -> CoreRule -> CoreFV
ruleFVs !_ BuiltinRule{} = emptyFV
ruleFVs from Rule{ ru_bndrs = bndrs, ru_rhs = rhs, ru_args = args }
  = filterFV isLocal $ addLamBndrsFV bndrs (exprsFVs exprs)

  where
    isLocal (In1 id) = isLocalId id
    isLocal _ = True

    exprs = case from of
      LhsOnly -> args
      RhsOnly -> [rhs]
      BothSides -> rhs:args

rulesFVs :: RuleFVsFrom -> [CoreRule] -> CoreFV
rulesFVs from = mapUnionFV (ruleFVs from)

rulesFreeVarsDSets :: [CoreRule] -> FVAnn
rulesFreeVarsDSets rules = fvDVarSets $ rulesFVs BothSides rules
