module CSlash.Core.DataCon where

import CSlash.Language.Syntax.Basic
import CSlash.Language.Syntax.Module.Name

import CSlash.Builtin.Types.Prim (mkTemplateTyVars, mkTemplateKindVars, mkTemplateFunKindVars)
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

import Data.ByteString (ByteString)
import qualified Data.ByteString.Builder as BSB
import qualified Data.ByteString.Lazy    as LBS
import qualified Data.Data as Data
import Data.Char
import Data.List( find )
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

instance Outputable (DataCon tv kv) where
  ppr con = ppr (dataConName con)

instance OutputableBndr (DataCon tv kv) where
  pprInfixOcc con = pprInfixName (dataConName con)
  pprPrefixOcc con = pprPrefixName (dataConName con)

instance (Data.Typeable tv, Data.Typeable kv) => Data.Data (DataCon tv kv) where
  toConstr _   = abstractConstr "DataCon"
  gunfold _ _  = error "gunfold"
  dataTypeOf _ = mkNoRepType "DataCon"

instance AsAnyTy DataCon where
  asAnyTy = panic "asAnyTy DataCon"

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

mkDataConTy :: TyCon tv kv -> Arity -> Type tv kv
mkDataConTy tycon arity = panic "dc_type"
  -- where
  --   fun_kind_vars = mkTemplateFunKindVars arity
  --   fun_kinds = KiVarKi <$> fun_kind_vars

  --   arg_kind_vars = mkTemplateKindVars arity
  --   arg_kinds = KiVarKi <$> arg_kind_vars
  --   ty_vars = mkTemplateTyVars arg_kinds
  --   tc_binders = mkSpecifiedTyConBinders ty_vars
  --   arg_tys = mkTyVarTys ty_vars

  --   res_type = mkTyConApp tycon arg_tys
  --   res_kind = case tyConResKind tycon of
  --                kd@(KiVarKi var)
  --                  | isKiVar var -> kd
  --                kc@(KiCon _) -> kc
  --                _ -> panic "mkDataConType: 'tyConResKind tycon' is not valid"

  --   arg_kind_constrs = (`LTEQKd` res_kind) <$> arg_kinds
  --   fun_kind_constrs = concatMap (\ (kf, i) ->
  --                                    let kds = take i arg_kinds
  --                                    in (`LTEQKd` kf) <$> kds)
  --                      $ fun_kinds `zip` [0..]
  --   full_constrs = KdContext $ arg_kind_constrs ++ fun_kind_constrs

  --   dc_partial_type = foldr2 FunTy res_type fun_kinds arg_tys
  --   dc_type = WithContext full_constrs $ foldr ForAllTy dc_partial_type tc_binders    

-- mkDataConTy
--   :: [TypeVar]     -- ^ type arguments
--   -> [ForAllTyBinder] -- ^ bound type arguments
--   -> [Type]        -- ^ types of value arguments
--   -> TyCon         -- ^ the tycon we're constructing
--   -> Type
-- mkDataConTy tyvars b_tyvars arg_tys tycon
--   = assert (binderVars b_tyvars == tyvars) dc_type
--   where
--     funKindVars = mkTemplateFunKindVars $ length arg_tys
--     funKinds = KiVarKi <$> funKindVars

--     types = Type.TyVarTy <$> tyvars
--     res_type = mkTyConApp tycon types
    
--     arg_ty_kinds = (\ty -> case ty of
--                              Type.TyVarTy tv 
--                                | isTypeVar tv -> varKind tv
--                              _ -> panic "mkDataConType: arg_ty is not 'TyVarTy (TyVar _ _ _)'")
--                    <$> arg_tys
--     res_kind = case tyConResKind tycon of
--                  kd@(KiVarKi var)
--                    | isKiVar var -> kd
--                  UKd -> UKd
--                  AKd -> AKd
--                  LKd -> LKd
--                  _ -> panic "mkDataConType: 'tyConResKind tycon' is not valid"
--     arg_ty_constrs =  (`LTEQKd` res_kind) <$> arg_ty_kinds
--     fun_kind_constrs = concatMap (\ (kf, i) ->
--                                      let kds = take i arg_ty_kinds
--                                      in (`LTEQKd` kf) <$> kds)
--                        $ funKinds `zip` [0..]
--     full_constrs = KdContext $ arg_ty_constrs ++ fun_kind_constrs

--     dc_partial_type = foldr2 FunTy res_type funKinds arg_tys
--     dc_type = WithContext full_constrs $ foldr ForAllTy dc_partial_type b_tyvars

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
