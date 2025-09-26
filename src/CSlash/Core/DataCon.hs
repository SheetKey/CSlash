{-# LANGUAGE RecordWildCards #-}

module CSlash.Core.DataCon where

import CSlash.Language.Syntax.Basic
import CSlash.Language.Syntax.Module.Name

import CSlash.Builtin.Types.Prim
import CSlash.Core.Type as Type
import CSlash.Core.Kind
import CSlash.Core.TyCon
import {-# SOURCE #-} CSlash.Types.TyThing
import CSlash.Types.SourceText
import CSlash.Types.Name
import CSlash.Builtin.Names
import CSlash.Types.Var
import CSlash.Types.Basic
import CSlash.Data.FastString
import CSlash.Unit.Types
import CSlash.Utils.Binary
import CSlash.Types.Unique.FM ( UniqFM )
import CSlash.Types.Unique.Set

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Trace

import Data.ByteString (ByteString)
import qualified Data.ByteString.Builder as BSB
import qualified Data.ByteString.Lazy    as LBS
import qualified Data.Data as Data
import Data.Char
import Data.List( find, inits )
import Numeric (showInt)

{- *********************************************************************
*                                                                      *
            Data constructors
*                                                                      *
********************************************************************* -}

-- NOTE:
-- If I add first class existentials
-- (i.e., pack/open or pack/unpack)
-- then I dot need (or want)
-- to have existentials in datacons.
-- INSTEAD:
-- we should have (invariant) length dcUnivTyVars <= length dcArgTys == length tyConBinders
-- '<=' since in GADTS, some tyvars in the datacon may be instantiated.

data DataCon tv kv = MkData
  { dcName :: Name
  , dcUnique :: Unique
  , dcTag :: ConTag
  , dcId :: Id tv kv
  , dcArity :: Arity
  , dcTyCon :: TyCon tv kv
  , dcType :: Type tv kv
  , dcInfix :: Bool
  }

type AnyDataCon = DataCon (AnyTyVar AnyKiVar) AnyKiVar

{- *********************************************************************
*                                                                      *
            Instances
*                                                                      *
********************************************************************* -}

instance Eq (DataCon tv kv) where
  a == b = getUnique a == getUnique b
  a /= b = getUnique a /= getUnique b

instance Uniquable (DataCon tv kv) where
  getUnique = dcUnique

instance NamedThing (DataCon tv kv) where
  getName = dcName

instance AsAnyTy DataCon where
  asAnyTyKi (MkData {..}) = MkData { dcId = asAnyTyKi dcId
                                   , dcTyCon = asAnyTyKi dcTyCon
                                   , dcType = asAnyTyKi dcType
                                   , .. }

instance Outputable (DataCon tv kv) where
  ppr con = ppr (dataConName con)

instance OutputableBndr (DataCon tv kv) where
  pprInfixOcc con = pprInfixName (dataConName con)
  pprPrefixOcc con = pprPrefixName (dataConName con)

instance (Data.Typeable tv, Data.Typeable kv) => Data.Data (DataCon tv kv) where
  toConstr _   = abstractConstr "DataCon"
  gunfold _ _  = error "gunfold"
  dataTypeOf _ = mkNoRepType "DataCon"

{- *********************************************************************
*                                                                      *
            Construction
*                                                                      *
********************************************************************* -}

mkDataCon
  :: Name
  -> Bool
  -> KnotTied (TyCon tv kv)
  -> ConTag
  -> Id tv kv
  -> Type tv kv
  -> Arity
  -> DataCon tv kv
mkDataCon name declared_infix tycon tag id ty arity
  = con
  where
    con = MkData { dcName = name
                 , dcUnique = nameUnique name
                 , dcInfix = declared_infix
                 , dcTyCon = tycon
                 , dcTag = tag
                 , dcType = ty
                 , dcId = id
                 , dcArity = arity
                 }

-- TyCon is the result type.
-- Arity is the number of term arguments
-- (does not include type args since builtin data-cons don't
-- have visible (only specified) type args)
-- This SHOULD NOT be used (as is) for Pattern Synonyms if we ever add them
-- Could change name to 'mkPcDataConTy' (them 'mkDataConTy', a more general version, would accempt arg types)
mkDataConTy :: PTyCon -> Arity -> PType 
mkDataConTy tycon arity = 
  pprTrace "mkDataConTy"
  (vcat [ ppr tycon
        , ppr arity
        , ppr tc_kind
        , ppr dc_type
        ]) $
  assert (arity == length fa_kvs - 1 && arity == length arg_kis) $
  dc_type
  where
    tc_kind = tyConKind tycon
    (fa_kvs, tc_mono_kind) = splitForAllKiVars tc_kind
    (ki_preds, tc_tau_kind) = splitInvisFunKis tc_mono_kind
    (arg_kis, res_ki) = splitFunKis tc_tau_kind

    -- make KiCoVars for preds and tvs from arity (using the kinds of fa_kvs (arity == length fa_kvs))
    -- make new KiVars for the arrow kinds
    -- want: /\fa_kvs -> forall kicos. forall tvs. tv1 -> ... -> tvn -> TyCon fa_kvs kicos tvs

    fun_ki_vars = mkTemplateFunKindVars arity
    fun_kis = KiVarKi <$> fun_ki_vars
    fun_ki_preds = let want_lts = inits arg_kis
                   in assert (length want_lts - 1 == length fun_kis) $
                      concat $ zipWith (fmap . (KiPredApp LTEQKi)) fun_kis want_lts

    final_preds = ki_preds ++ fun_ki_preds
    kcos = mkTemplateKiCoVars final_preds

    arg_ty_vars = mkTemplateTyVars arg_kis
    arg_tys = TyVarTy <$> arg_ty_vars

    ffoldr :: (a -> b -> b) -> [a] -> b -> b
    ffoldr f l r = foldr f r l
    
    dc_type = ffoldr BigTyLamTy fa_kvs $ -- /\k1..kn ->
              ffoldr ForAllTy ((flip Bndr Specified) <$> kcos) $ -- forall kco1..kcon.
              ffoldr ForAllTy ((flip Bndr Specified) <$> arg_ty_vars) $ -- forall a..b.
              ffoldr (uncurry FunTy) (zip fun_kis arg_tys) $ -- a -> .. -> b ->
              mkTyConApp tycon $ (Embed . KiVarKi <$> fa_kvs)
                              ++ (TyVarTy <$> kcos) -- maybe should be KindCoercion (mkKiCoVarCo <$> kcos) ??
                              ++ arg_tys

dataConName :: DataCon tv kv -> Name
dataConName = dcName

dataConTyCon :: DataCon tv kv -> TyCon tv kv
dataConTyCon = dcTyCon

dataConType :: DataCon tv kv -> Type tv kv
dataConType = dcType
         
dataConArity :: DataCon tv kv -> Arity
dataConArity (MkData { dcArity = arity }) = arity

dataConId :: DataCon tv kv -> Id tv kv
dataConId dc = dcId dc

dataConImplicitTyThing :: DataCon tv kv -> TyThing tv kv
dataConImplicitTyThing (MkData { dcId = id }) = mkAnId id

dataConFullSig :: DataCon tv kv -> Type tv kv
dataConFullSig (MkData { dcType = full_ty }) = full_ty
