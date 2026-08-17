{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RoleAnnotations #-}

module CSlash.Core.Type.Rep where

import {-# SOURCE #-} CSlash.Core.TyCon (TyCon)

import CSlash.Cs.Pass

import CSlash.Utils.Outputable (Outputable)
import CSlash.Utils.FV

import qualified Data.Data as Data

type role Type nominal
data Type tv 

instance Data.Data tv => Data.Data (Type tv)

type PredType = Type

mkNakedTyConTy :: TyCon p -> Type p

instance IsPass p => Outputable (Type (CsPass p))

-- instance HasFVs (Type p) where
--   -- type FVInScope (Type p) = (TyVarSet p, KiCoVarSet p, KiVarSet p)
--   type FVAcc (Type p) = ([TyVar p], TyVarSet p, [KiCoVar p], KiCoVarSet p, [KiVar p], KiVarSet p)
--   -- type FVArg (Type p) = E3 (TyVar p) (KiCoVar p) (KiVar p)

--   -- fvElemAcc (In1 tv) (_, haveSet, _, _, _, _) = tv `elemVarSet` haveSet
--   -- fvElemAcc (In2 kcv) (_, _, _, haveSet, _, _) = kcv `elemVarSet` haveSet
--   -- fvElemAcc (In3 kv) (_, _, _, _, _, haveSet) = kv `elemVarSet` haveSet

--   -- fvElemIS (In1 tv) (in_scope, _, _) = tv `elemVarSet` in_scope
--   -- fvElemIS (In2 kcv) (_, in_scope, _) = kcv `elemVarSet` in_scope
--   -- fvElemIS (In3 kv) (_, _, in_scope) = kv `elemVarSet` in_scope

--   -- fvExtendAcc (In1 tv) (have, haveSet, kcs, kcset, ks, kset)
--   --   = (tv:have, extendVarSet haveSet tv, kcs, kcset, ks, kset)
--   -- fvExtendAcc (In2 kcv) (ts, tset, have, haveSet, ks, kset)
--   --   = (ts, tset, kcv:have, extendVarSet haveSet kcv, ks, kset)
--   -- fvExtendAcc (In3 kv) (ts, tset, kcs, kcset, have, haveSet)
--   --   = (ts, tset, kcs, kcset, kv:have, extendVarSet haveSet kv)

--   -- fvExtendIS (In1 tv) (in_scope, kcs, ks) = (extendVarSet in_scope tv, kcs, ks)
--   -- fvExtendIS (In2 kcv) (ts, in_scope, ks) = (ts, extendVarSet in_scope kcv, ks)
--   -- fvExtendIS (In3 kv) (ts, kcs, in_scope) = (ts, kcs, extendVarSet in_scope kv)

--   -- fvEmptyAcc = ([], emptyVarSet, [], emptyVarSet, [], emptyVarSet)
--   -- fvEmptyIS = (emptyVarSet, emptyVarSet, emptyVarSet)
