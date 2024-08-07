module CSlash.Builtin.Types where

import {-# SOURCE #-} CSlash.Types.Id.Make (mkDataConWorkId)

import CSlash.Builtin.Names
import CSlash.Builtin.Types.Prim
import CSlash.Builtin.Uniques

import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Types.Id
import CSlash.Core.DataCon
import CSlash.Core.TyCon
import qualified CSlash.Core.Type.Rep as TypeRep (Type(TyConApp))

import CSlash.Types.TyThing
import CSlash.Types.SourceText
import CSlash.Types.Var (VarBndr(Bndr), tyVarName)
import CSlash.Types.Name.Reader
import CSlash.Types.Name as Name
import CSlash.Types.Name.Env (lookupNameEnv_NF, mkNameEnv)
import CSlash.Types.Basic
import CSlash.Types.Unique.Set

import CSlash.Settings.Constants (mAX_TUPLE_SIZE, mAX_SUM_SIZE)
import CSlash.Unit.Module (Module)

import Data.Array
import CSlash.Data.FastString

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic

import qualified Data.ByteString.Char8 as BS

import Numeric (showInt)

{- *********************************************************************
*                                                                      *
            Wired in type constructors
*                                                                      *
********************************************************************* -}

mkWiredInTyConName :: BuiltInSyntax -> Module -> FastString -> Unique -> TyCon -> Name
mkWiredInTyConName built_in modu fs unique tycon
  = mkWiredInName modu (mkTcOccFS fs) unique (ATyCon tycon) built_in

mkWiredInDataConName :: BuiltInSyntax -> Module -> FastString -> Unique -> DataCon -> Name
mkWiredInDataConName built_in modu fs unique datacon
  = mkWiredInName modu (mkDataOccFS fs) unique (ADataCon datacon) built_in

mkWiredInIdName :: Module -> FastString -> Unique -> Id -> Name
mkWiredInIdName modu fs unique id
  = mkWiredInName modu (mkOccNameFS Name.varName fs) unique (AnId id) UserSyntax

boolTyConName :: Name
boolTyConName = mkWiredInTyConName UserSyntax cSLASH_TYPES (fsLit "Bool") boolTyConKey boolTyCon

falseDataConName :: Name
falseDataConName
  = mkWiredInDataConName UserSyntax cSLASH_TYPES (fsLit "False") falseDataConKey falseDataCon

trueDataConName :: Name
trueDataConName
  = mkWiredInDataConName UserSyntax cSLASH_TYPES (fsLit "True") trueDataConKey trueDataCon

{- *********************************************************************
*                                                                      *
            mkWiredInTyCon
*                                                                      *
********************************************************************* -}

-- assumes types have unrestricted kind
pcTyCon :: Name -> [TypeVar] -> [DataCon] -> TyCon
pcTyCon name tyvars cons
  = mkAlgTyCon name
               (mkSpecifiedTyConBinders tyvars)
               UKd
               (mkDataTyConRhs cons)
               VanillaAlgTyCon

pcDataCon :: Name -> [TypeVar] -> [Type] -> TyCon -> DataCon
pcDataCon n univs tys tycon
  = pcDataConWithFixity False n univs [] tys tycon

pcDataConWithFixity
  :: Bool -- declared infix?
  -> Name
  -> [TypeVar] -- univ tyvars
  -> [TypeVar] -- ex tyvars
  -> [Type] -- args
  -> TyCon
  -> DataCon
pcDataConWithFixity infx n = pcDataConWithFixity' infx n (dataConWorkerUnique (nameUnique n))

pcDataConWithFixity'
  :: Bool
  -> Name
  -> Unique
  -> [TypeVar]
  -> [TypeVar]
  -> [Type]
  -> TyCon
  -> DataCon
pcDataConWithFixity' declared_infix dc_name wrk_key tyvars ex_tyvars arg_tys tycon
  = data_con
  where
    tag_map = mkTyConTagMap tycon
    data_con = mkDataCon dc_name
                         declared_infix
                         tyvars
                         arg_tys
                         (mkTyConApp tycon (mkTyVarTys tyvars))
                         tycon
                         (lookupNameEnv_NF tag_map dc_name)
                         (mkDataConWorkId wrk_name data_con)
    wrk_name = mkDataConWorkerName data_con wrk_key

mkDataConWorkerName :: DataCon -> Unique -> Name
mkDataConWorkerName data_con wrk_key =
    mkWiredInName modu wrk_occ wrk_key (AnId (dataConWorkId data_con)) UserSyntax
  where
    modu = assert (isExternalName dc_name) $ nameModule dc_name
    dc_name = dataConName data_con
    dc_occ = nameOccName dc_name
    wrk_occ = mkDataConWorkerOcc dc_occ

{- *********************************************************************
*                                                                      *
            Tuples
*                                                                      *
********************************************************************* -}

mkTupleOcc :: NameSpace -> Arity -> OccName
mkTupleOcc ns ar = mkOccName ns (mkTupleStr ns ar)

mkTupleStr :: NameSpace -> Arity -> String
mkTupleStr ns 0
  | isDataConNameSpace ns = "()"
  | otherwise = "Unit"
mkTupleStr ns 1
  | isDataConNameSpace ns = "MkSolo"
  | otherwise = "Solo"
mkTupleStr ns ar
  | isDataConNameSpace ns = '(' : commas ar ++ ")"
  | otherwise = "Tuple" ++ showInt ar ""

commas :: Arity -> String
commas ar = replicate (ar-1) ','

tupleTyCon :: Arity -> TyCon
tupleTyCon i
  | i > mAX_TUPLE_SIZE = fst (mk_tuple i)
  | otherwise = fst (tupleArr ! i)

tupleTyConName :: Arity -> Name
tupleTyConName a = tyConName (tupleTyCon a)

tupleDataCon :: Arity -> DataCon
tupleDataCon i
  | i > mAX_TUPLE_SIZE = snd (mk_tuple i)
  | otherwise = snd (tupleArr ! i)

tupleDataConName :: Arity -> Name
tupleDataConName i = dataConName (tupleDataCon i)

tupleArr :: Array Int (TyCon, DataCon)
tupleArr = listArray (0, mAX_TUPLE_SIZE) [mk_tuple i | i <- [0..mAX_TUPLE_SIZE]]

mk_tuple :: Int -> (TyCon, DataCon)
mk_tuple arity = (tycon, tuple_con)
  where
    tycon = mkTupleTyCon tc_name tc_binders tc_kind tuple_con flavor
    -- (kind_vars, res_kind_var) = mkTemplateKindVars arity
    -- kinds = KdVarKd <$> kind_vars
    -- res_kind = KdVarKd res_kind_var
    -- tc_binders = mkTemplateTyConBinders kinds
    -- tc_kind_constrs = KdContext $ (`LTEQKd` res_kind) <$> kinds
    -- tc_kind = FunKd FKF_C_K tc_kind_constrs $ foldr (FunKd FKF_K_K) res_kind kinds
    (tc_binders, tc_kind) = mkTemplateTyConBindersKindLTEQ arity

    dc_tvs = binderVars tc_binders
    dc_arg_tys = mkTyVarTys dc_tvs
    flavor = VanillaAlgTyCon
    tuple_con = pcDataCon dc_name dc_tvs dc_arg_tys tycon
    
    modu = cSLASH_TYPES
    tc_name = mkWiredInName modu (mkTupleOcc tcName arity) tc_uniq
                            (ATyCon tycon) UserSyntax
    tc_uniq = mkTupleTyConUnique arity
    dc_name = mkWiredInName modu (mkTupleOcc dataName arity) dc_uniq
                            (ADataCon tuple_con) BuiltInSyntax
    dc_uniq = mkTupleDataConUnique arity

{- *********************************************************************
*                                                                      *
              The Bool type
*                                                                      *
********************************************************************* -}

boolTy :: Type
boolTy = mkTyConTy boolTyCon

boolTyCon :: TyCon
boolTyCon = pcTyCon boolTyConName
                    -- Nothing
                    [] [falseDataCon, trueDataCon]

falseDataCon :: DataCon
falseDataCon = pcDataCon falseDataConName [] [] boolTyCon

trueDataCon :: DataCon
trueDataCon = pcDataCon trueDataConName [] [] boolTyCon


