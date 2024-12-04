{-# LANGUAGE OverloadedStrings #-}

module CSlash.Builtin.Types where

import {-# SOURCE #-} CSlash.Types.Id.Make (mkDataConWorkId)

import CSlash.Builtin.Names
import CSlash.Builtin.Types.Prim
import CSlash.Builtin.Uniques

import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Types.Id
import CSlash.Core.DataCon
import CSlash.Core.ConLike
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

import Data.List (intersperse)
import Numeric (showInt)

import Data.Char (ord, isDigit)
import Control.Applicative ((<|>))

{- *********************************************************************
*                                                                      *
            Wired in type constructors
*                                                                      *
********************************************************************* -}

wiredInTyCons :: [TyCon]
wiredInTyCons
  = [ boolTyCon ]

mkWiredInTyConName :: BuiltInSyntax -> Module -> FastString -> Unique -> TyCon -> Name
mkWiredInTyConName built_in modu fs unique tycon
  = mkWiredInName modu (mkTcOccFS fs) unique (ATyCon tycon) built_in

mkWiredInDataConName :: BuiltInSyntax -> Module -> FastString -> Unique -> DataCon -> Name
mkWiredInDataConName built_in modu fs unique datacon
  = mkWiredInName modu (mkDataOccFS fs) unique (AConLike (RealDataCon datacon)) built_in

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

-- assumes types have ANY kind (I.e., a kind var)
pcTyCon :: Name -> [TypeVar] -> [DataCon] -> TyCon
pcTyCon name tyvars cons
  = mkAlgTyCon name
               (mkSpecifiedTyConBinders tyvars)
               (KiVarKi mkTemplateKindVar)
               (KiVarKi mkTemplateKindVar)
               (mkDataTyConRhs cons)
               VanillaAlgTyCon

pcDataCon :: Name -> [TypeVar] -> [ForAllTyBinder] ->[Type] -> TyCon -> DataCon
pcDataCon n univs b_univs tys tycon
  = pcDataConWithFixity False n univs b_univs tys tycon

pcDataConWithFixity
  :: Bool -- declared infix?
  -> Name
  -> [TypeVar] -- univ tyvars
  -> [ForAllTyBinder] -- bound univ tyvars
  -> [Type] -- types of args
  -> TyCon
  -> DataCon
pcDataConWithFixity infx n = pcDataConWithFixity' infx n (dataConWorkerUnique (nameUnique n))

pcDataConWithFixity'
  :: Bool
  -> Name
  -> Unique
  -> [TypeVar]
  -> [ForAllTyBinder]
  -> [Type]
  -> TyCon
  -> DataCon
pcDataConWithFixity' declared_infix dc_name wrk_key tyvars b_tyvars arg_tys tycon
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
                         dc_ty
    wrk_name = mkDataConWorkerName data_con wrk_key
    dc_ty = mkDataConTy tyvars b_tyvars arg_tys tycon

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

isBuiltInOcc_maybe :: OccName -> Maybe Name
isBuiltInOcc_maybe occ =
  case name of
    "FUN" -> Just fUNTyConName
    "->" -> panic "isBuiltInOcc_maybe: ->"

    "()" -> Just $ tup_name 0
    _ | Just rest <- "(" `BS.stripPrefix` name
      , (commas, rest') <- BS.span (== ',') rest
      , ")" <- rest'
        -> Just $ tup_name (1 + BS.length commas)

    _ | Just rest <- "(" `BS.stripPrefix` name
      , (nb_pipes, rest') <- span_pipes rest
      , ")" <- rest'
        -> Just $ tyConName $ sumTyCon (1 + nb_pipes)

    _ | Just rest <- "(" `BS.stripPrefix` name
      , (nb_pipes1, rest') <- span_pipes rest
      , Just rest'' <- "_" `BS.stripPrefix` rest'
      , (nb_pipes2, rest''') <- span_pipes rest''
      , ")" <- rest'''
        -> let arity = nb_pipes1 + nb_pipes2 + 1
               alt = nb_pipes1 + 1
           in Just $ dataConName $ sumDataCon alt arity
    _ -> Nothing
  where
    name = bytesFS $ occNameFS occ

    span_pipes :: BS.ByteString -> (Int, BS.ByteString)
    span_pipes = go 0
      where
        go nb_pipes bs = case BS.uncons bs of
                           Just ('|', rest) -> go (nb_pipes + 1) rest
                           Just (' ', rest) -> go nb_pipes rest
                           _ -> (nb_pipes, bs)

    choose_ns :: Name -> Name -> Name
    choose_ns tc dc
      | isTcClsNameSpace ns = tc
      | isDataConNameSpace ns = dc
      | otherwise = pprPanic "tup_name" (ppr occ <+> parens (pprNameSpace ns))
      where ns = occNameSpace occ

    tup_name arity = choose_ns (getName (tupleTyCon arity))
                               (getName (tupleDataCon arity))

isTupleTyOcc_maybe :: Module -> OccName -> Maybe Name
isTupleTyOcc_maybe mod occ
  | mod == cSLASH_TYPES
  = match_occ
  where
    match_occ
      | occ == occName unitTyConName = Just unitTyConName
      | occ == occName soloTyConName = Just soloTyConName
      | otherwise = isTupleNTyOcc_maybe occ
isTupleTyOcc_maybe _ _ = Nothing

isTupleNTyOcc_maybe :: OccName -> Maybe Name
isTupleNTyOcc_maybe occ =
  case occNameString occ of
    'T':'u':'p':'l':'e':str | Just n <- arity_from_str str, n > 1
                              -> Just (tupleTyConName n)
    _ -> Nothing

isSumTyOcc_maybe :: Module -> OccName -> Maybe Name
isSumTyOcc_maybe mod occ
  | mod == cSLASH_TYPES
  = isSumNTyOcc_maybe occ
isSumTyOcc_maybe _ _ = Nothing

isSumNTyOcc_maybe :: OccName -> Maybe Name
isSumNTyOcc_maybe occ =
  case occNameString occ of
    'S':'u':'m':str | Just n <- arity_from_str str, n > 1
                      -> Just (tyConName (sumTyCon n))
    _ -> Nothing

arity_from_str :: String -> Maybe Int
arity_from_str s = case s of
  c1 : t1 | isDigit c1 -> case t1 of
                            [] -> Just $ digit_to_int c1
                            c2 : t2 | isDigit c2 ->
                                        let ar = digit_to_int c1 * 10 + digit_to_int c2
                                        in case t2 of
                                             [] -> Just ar
                                             _ -> Nothing
                            _ -> Nothing
  _ -> Nothing
  where
    digit_to_int :: Char -> Int
    digit_to_int c = ord c - ord '0'

isPunOcc_maybe :: Module -> OccName -> Maybe Name
isPunOcc_maybe mod occ
  | mod == cSLASH_TYPES, occ == occName soloDataConName
  = Just soloDataConName
  | otherwise
  = isTupleTyOcc_maybe mod occ <|>
    isSumTyOcc_maybe mod occ

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
    tycon = mkTupleTyCon tc_name tc_binders tc_res_kind tc_kind tuple_con flavor

    (tc_binders, tc_res_kind, tc_kind) = mkTemplateTyConBindersKind arity

    dc_tvs = binderVars tc_binders
    dc_arg_tys = mkTyVarTys dc_tvs
    flavor = VanillaAlgTyCon
    tuple_con = pcDataCon dc_name dc_tvs tc_binders dc_arg_tys tycon
    
    modu = cSLASH_TYPES
    tc_name = mkWiredInName modu (mkTupleOcc tcName arity) tc_uniq
                            (ATyCon tycon) UserSyntax
    tc_uniq = mkTupleTyConUnique arity
    dc_name = mkWiredInName modu (mkTupleOcc dataName arity) dc_uniq
                            (AConLike (RealDataCon tuple_con)) BuiltInSyntax
    dc_uniq = mkTupleDataConUnique arity

unitTyCon :: TyCon
unitTyCon = tupleTyCon 0

unitTyConName :: Name
unitTyConName = tyConName unitTyCon

unitTyConKey :: Unique
unitTyConKey = getUnique unitTyCon

unitDataCon :: DataCon
unitDataCon = head (tyConDataCons unitTyCon)

unitDataConId :: Id
unitDataConId = dataConWorkId unitDataCon

soloTyCon :: TyCon
soloTyCon = tupleTyCon 1

soloTyConName :: Name
soloTyConName = tyConName soloTyCon

soloDataConName :: Name
soloDataConName = tupleDataConName 1

{- *********************************************************************
*                                                                      *
      Sums
*                                                                      *
********************************************************************* -}

mkSumTyConOcc :: Arity -> OccName
mkSumTyConOcc n = mkOccName tcName str
  where
    str = "Sum" ++ show n

mkSumDataConOcc :: ConTag -> Arity -> OccName
mkSumDataConOcc alt n = mkOccName dataName str
  where
    str = '(' : ' ' : bars alt ++ '_' : bars (n - alt - 1) ++ " )"
    bars i = intersperse ' ' $ replicate i '|'

sumTyCon :: Arity -> TyCon
sumTyCon arity
  | arity > mAX_SUM_SIZE
  = fst (mk_sum arity)
  | arity < 2
  = panic ("sumTyCon: Arity start from 2. (arity: " ++ show arity ++ ")")
  |otherwise
  = fst (sumArr ! arity)

sumDataCon :: ConTag -> Arity -> DataCon
sumDataCon alt arity
  | alt > arity
  = panic ("sumDataCon: index out of bounds: alt: "
           ++ show alt ++ " > arity " ++ show arity)
  | alt <= 0
  = panic ("sumDataCon: Alts start from 1. (alt: " ++ show alt
           ++ ", arity: " ++ show arity ++ ")")
  | arity < 2
  = panic ("sumDataCon: Arity starts from 2. (alt: " ++ show alt
           ++ ", arity: " ++ show arity ++ ")")
  | arity > mAX_SUM_SIZE
  = snd (mk_sum arity) ! (alt - 1)
  | otherwise
  = snd (sumArr ! arity) ! (alt - 1)

sumArr :: Array Int (TyCon, Array Int DataCon)
sumArr = listArray (2, mAX_SUM_SIZE) [mk_sum i | i <- [2..mAX_SUM_SIZE]]

mk_sum :: Arity -> (TyCon, Array ConTagZ DataCon)
mk_sum arity = (tycon, sum_cons)
  where
    tycon = mkSumTyCon tc_name tc_binders tc_res_kind tc_kind (elems sum_cons) AlgSumTyCon
  
    (tc_binders, tc_res_kind, tc_kind) = mkTemplateTyConBindersKind arity

    dc_tvs = binderVars tc_binders
    dc_arg_tys = mkTyVarTys dc_tvs

    modu = cSLASH_TYPES
    tc_name = mkWiredInName modu (mkSumTyConOcc arity) tc_uniq
                            (ATyCon tycon) UserSyntax

    sum_cons = listArray (0, arity - 1) [sum_con i | i <- [0..arity-1]]
    sum_con i =
      let dc = pcDataCon dc_name dc_tvs tc_binders [dc_arg_tys !! i] tycon
          dc_name = mkWiredInName modu (mkSumDataConOcc i arity) (dc_uniq i)
                                  (AConLike (RealDataCon dc)) BuiltInSyntax
      in dc
      
    tc_uniq = mkSumTyConUnique arity
    dc_uniq i = mkSumDataConUnique i arity

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
falseDataCon = pcDataCon falseDataConName [] [] [] boolTyCon

trueDataCon :: DataCon
trueDataCon = pcDataCon trueDataConName [] [] [] boolTyCon


