{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

module CSlash.Core.FVs where

import CSlash.Cs.Pass

import CSlash.Core as Core
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.Name.Set
import CSlash.Types.Name
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

bndrUnfoldingFVs :: CoreBndr -> CoreFV
bndrUnfoldingFVs (Core.Id id) = idUnfoldingFVs id
bndrUnfoldingFVs _ = emptyFV

idUnfoldingFVs :: CoreId -> CoreFV
idUnfoldingFVs id = stableUnfoldingFVs (realIdUnfolding id) `orElse` emptyFV
 
stableUnfoldingFVs :: Unfolding -> Maybe CoreFV
stableUnfoldingFVs unf = case unf of
  CoreUnfolding { uf_tmpl = rhs, uf_src = src }
    | isStableSource src -> Just (exprLocalFVs rhs)
    | otherwise -> Nothing
  NoUnfolding -> Nothing
  OtherCon {} -> Nothing
