{-# LANGUAGE OverloadedStrings #-}

module CSlash.Builtin.Types where

import {-# SOURCE #-} CSlash.Types.Id.Make (mkDataConId)

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
import CSlash.Types.Var (VarBndr(Bndr), varName)
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

-- Should be in TyCon module but would require importing BuiltIn.Prim (module loop)
tyConTyKiVars :: TyCon (TyVar KiVar) KiVar -> ([KiVar], [TyVar KiVar])
tyConTyKiVars tc =
  let tc_kind = tyConKind tc
      (kvs, mki) = splitForAllKiVars tc_kind
      (kis, _) = splitMonoFunKis mki
      tvs = mkTemplateTyVars kis
  in (kvs, tvs)

{- *********************************************************************
*                                                                      *
            Wired in type constructors
*                                                                      *
********************************************************************* -}

type PDataCon = DataCon PTyVar KiVar
type PId = Id PTyVar KiVar

wiredInTyCons :: [PTyCon]
wiredInTyCons
  = [ unitTyCon
    , soloTyCon
    , boolTyCon
    ]

mkWiredInTyConName :: BuiltInSyntax -> Module -> FastString -> Unique -> PTyCon -> Name
mkWiredInTyConName built_in modu fs unique tycon
  = mkWiredInName modu (mkTcOccFS fs) unique (ATyCon tycon) built_in

mkWiredInDataConName :: BuiltInSyntax -> Module -> FastString -> Unique -> PDataCon -> Name
mkWiredInDataConName built_in modu fs unique datacon
  = mkWiredInName modu (mkDataOccFS fs) unique (AConLike (RealDataCon datacon)) built_in

mkWiredInIdName :: Module -> FastString -> Unique -> PId -> Name
mkWiredInIdName modu fs unique id
  = mkWiredInName modu (mkOccNameFS Name.varName fs) unique (AnId id) UserSyntax

boolTyConName :: Name
boolTyConName = mkWiredInTyConName UserSyntax cSLASH_BUILTIN (fsLit "Bool") boolTyConKey boolTyCon

falseDataConName :: Name
falseDataConName
  = mkWiredInDataConName UserSyntax cSLASH_BUILTIN (fsLit "False") falseDataConKey falseDataCon

trueDataConName :: Name
trueDataConName
  = mkWiredInDataConName UserSyntax cSLASH_BUILTIN (fsLit "True") trueDataConKey trueDataCon

makeRecoveryTyCon :: PTyCon -> PTyCon
makeRecoveryTyCon tc = panic "makeRecoveryTyCon"
  -- mkTcTyCon (tyConName tc)
  --                                (tyConKind tc)
  --                                (tyConArity tc)
  --                                []
  --                                True
  --                                (tyConFlavor tc)

{- *********************************************************************
*                                                                      *
            mkWiredInTyCon
*                                                                      *
********************************************************************* -}

-- assumes types have ANY kind (I.e., a kind var)
pcTyCon :: Name -> [PDataCon] -> Arity -> PTyCon
pcTyCon name cons arity
  = mkAlgTyCon name
               kind
               arity
               (mkDataTyConRhs cons)
               VanillaAlgTyCon
  where
    kind = mkTemplateTyConKind arity

pcDataCon :: Name -> PTyCon -> Arity -> PDataCon
pcDataCon n tycon arity
  = pcDataConWithFixity False n tycon arity

pcDataConWithFixity
  :: Bool -- declared infix?
  -> Name
  -> PTyCon
  -> Arity
  -> PDataCon
pcDataConWithFixity infx n = pcDataConWithFixity' infx n (dataConUnique (nameUnique n))

pcDataConWithFixity'
  :: Bool
  -> Name
  -> Unique
  -> PTyCon
  -> Arity
  -> PDataCon
pcDataConWithFixity' declared_infix dc_name key tycon arity
  = data_con
  where
    tag_map = mkTyConTagMap tycon
    data_con = mkDataCon dc_name
                         declared_infix
                         tycon
                         (lookupNameEnv_NF tag_map dc_name)
                         (mkDataConId name data_con)
                         dc_ty
                         arity
    name = mkDataConName data_con key
    dc_ty = mkDataConTy tycon arity

mkDataConName :: PDataCon -> Unique -> Name
mkDataConName data_con key =
    mkWiredInName modu occ key (AnId (dataConId data_con)) UserSyntax
  where
    modu = assert (isExternalName dc_name) $ nameModule dc_name
    dc_name = dataConName data_con
    dc_occ = nameOccName dc_name
    occ = mkDataConOcc dc_occ

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
  | mod == cSLASH_BUILTIN
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
  | mod == cSLASH_BUILTIN
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
  | mod == cSLASH_BUILTIN, occ == occName soloDataConName
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

tupleTyCon :: Arity -> PTyCon
tupleTyCon i
  | i > mAX_TUPLE_SIZE = fst (mk_tuple i)
  | otherwise = fst (tupleArr ! i)

tupleTyConName :: Arity -> Name
tupleTyConName a = tyConName (tupleTyCon a)

tupleDataCon :: Arity -> PDataCon
tupleDataCon i
  | i > mAX_TUPLE_SIZE = snd (mk_tuple i)
  | otherwise = snd (tupleArr ! i)

tupleDataConName :: Arity -> Name
tupleDataConName i = dataConName (tupleDataCon i)

tupleArr :: Array Int (PTyCon, PDataCon)
tupleArr = listArray (0, mAX_TUPLE_SIZE) [mk_tuple i | i <- [0..mAX_TUPLE_SIZE]]

mk_tuple :: Int -> (PTyCon, PDataCon)
mk_tuple arity = (tycon, tuple_con)
  where
    tycon = mkTupleTyCon tc_name tc_kind arity tuple_con flavor

    tc_kind = mkTemplateTyConKind arity

    flavor = VanillaAlgTyCon
    tuple_con = pcDataCon dc_name tycon arity
    
    modu = cSLASH_BUILTIN
    tc_name = mkWiredInName modu (mkTupleOcc tcName arity) tc_uniq
                            (ATyCon tycon) UserSyntax
    tc_uniq = mkTupleTyConUnique arity
    dc_name = mkWiredInName modu (mkTupleOcc dataName arity) dc_uniq
                            (AConLike (RealDataCon tuple_con)) BuiltInSyntax
    dc_uniq = mkTupleDataConUnique arity

unitTyCon :: PTyCon
unitTyCon = tupleTyCon 0

unitTyConName :: Name
unitTyConName = tyConName unitTyCon

unitTyConKey :: Unique
unitTyConKey = getUnique unitTyCon

unitDataCon :: PDataCon
unitDataCon = head (tyConDataCons unitTyCon)

unitDataConId :: PId
unitDataConId = dataConId unitDataCon

unitDataConName :: Name
unitDataConName = dataConName unitDataCon

soloTyCon :: PTyCon
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

sumTyCon :: Arity -> PTyCon
sumTyCon arity
  | arity > mAX_SUM_SIZE
  = fst (mk_sum arity)
  | arity < 2
  = panic ("sumTyCon: Arity start from 2. (arity: " ++ show arity ++ ")")
  |otherwise
  = fst (sumArr ! arity)

sumDataCon :: ConTag -> Arity -> PDataCon
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

sumArr :: Array Int (PTyCon, Array Int PDataCon)
sumArr = listArray (2, mAX_SUM_SIZE) [mk_sum i | i <- [2..mAX_SUM_SIZE]]

mk_sum :: Arity -> (PTyCon, Array ConTagZ PDataCon)
mk_sum arity = (tycon, sum_cons)
  where
    tycon = mkSumTyCon tc_name tc_kind arity (elems sum_cons) AlgSumTyCon
  
    tc_kind = mkTemplateTyConKind arity

    modu = cSLASH_BUILTIN
    tc_name = mkWiredInName modu (mkSumTyConOcc arity) tc_uniq
                            (ATyCon tycon) UserSyntax

    sum_cons = listArray (0, arity - 1) [sum_con i | i <- [0..arity-1]]
    sum_con i =
      let dc = pcDataCon dc_name tycon 1
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

boolTy :: PType
boolTy = mkTyConTy boolTyCon

boolTyCon :: PTyCon
boolTyCon = pcTyCon boolTyConName [falseDataCon, trueDataCon] 0

falseDataCon :: PDataCon
falseDataCon = pcDataCon falseDataConName boolTyCon 0

trueDataCon :: PDataCon
trueDataCon = pcDataCon trueDataConName boolTyCon 0

{- *********************************************************************
*                                                                      *
              IO
*                                                                      *
********************************************************************* -}

{-
The 'IORes' tycon has kind
type IORes : ∀ k. k -> ○

The 'MkIORes' datacon has type
data MkIORes : /\k k2 -> ∀ {kco : k2 <= k}. ∀ {a : k}. a -★> RealWorld# -k2> (IORes {k} a : ○)

The 'MkIORes' data can be thought of as the function
data MkIORes
  = /\{k} {k2} -> /\{kco : (k2 <= k)} -> /\{a : k} -> \a -> \(x : RealWorld#) -> (a, x)
-}
ioResTyConName :: Name
ioResTyConName
  = mkWiredInTyConName UserSyntax cSLASH_BUILTIN
    (fsLit "IORes") ioResTyConKey ioResTyCon

mkIoResDataConName :: Name
mkIoResDataConName
  = mkWiredInDataConName UserSyntax cSLASH_BUILTIN
    (fsLit "MkIORes") mkIoResDataConKey mkIoResDataCon

ioResTyCon :: PTyCon
ioResTyCon
  = mkAlgTyCon ioResTyConName kind arity (mkDataTyConRhs [mkIoResDataCon]) VanillaAlgTyCon
  where
    arity = 1

    kva = case mkTemplateKindVars 1 of
            [k1] -> k1
            _ -> panic "unreachable"
    kind = ForAllKi kva $
           Mono $ FunKi FKF_K_K (KiVarKi kva) (BIKi LKd)

mkIoResDataCon :: PDataCon
mkIoResDataCon = data_con
  where
    tag_map = mkTyConTagMap ioResTyCon
    data_con = mkDataCon mkIoResDataConName
                         False
                         ioResTyCon
                         (lookupNameEnv_NF tag_map mkIoResDataConName)
                         (mkDataConId name data_con)
                         dc_ty
                         2
    name = mkDataConName data_con mkIoResDataConKey
    dc_ty = let kva = case mkTemplateKindVars 1 of
                        [k1] -> k1
                        _ -> panic "unreachable"
                kvf = case mkTemplateFunKindVars 1 of
                        [k1] -> k1
                        _ -> panic "unreachable"

                ka = KiVarKi kva
                kf = KiVarKi kvf

                va = case mkTemplateTyVars [ka] of
                       [a] -> a
                       _ -> panic "unreachable"
                a = TyVarTy va

                pred = KiPredApp LTEQKi kf ka
                kco = case mkTemplateKiCoVars [pred] of
                        [kco] -> kco
                        _ -> panic "unreachable"

                dc_type = BigTyLamTy kva $
                          BigTyLamTy kvf $
                          ForAllTy (Bndr kco Specified) $
                          ForAllTy (Bndr va Specified) $
                          FunTy (BIKi UKd) a $ 
                          FunTy kf (mkTyConTy realWorldTyCon) $
                          mkTyConApp ioResTyCon [ Embed ka, a ]
            in dc_type

{-
The 'PrimIO' type synonym is defined as
type PrimIO : ∀ k kf. k -> kf
type PrimIO = /\ k kf -> \ (a : k) -> RealWorld# -kf> IORes {k} a
-}

primIoTyConName :: Name
primIoTyConName
  = mkWiredInTyConName UserSyntax cSLASH_BUILTIN
    (fsLit "PrimIO") primIoTyConKey primIoTyCon

primIoTyCon :: PTyCon
primIoTyCon = buildSynTyCon primIoTyConName kind 1 rhs
  where
    kva = case mkTemplateKindVars 1 of
            [k1] -> k1
            _ -> panic "unreachable"
    kvf = case mkTemplateFunKindVars 1 of
            [k] -> k
            _ -> panic "unreachable"

    tva = case mkTemplateTyVars [mkKiVarKi kva] of
            [tv] -> tv
            _ -> panic "unreachable"

    kind = typeKind rhs

    rhs = BigTyLamTy kva $
          BigTyLamTy kvf $
          TyLamTy tva $
          FunTy (KiVarKi kvf)
                (mkTyConTy realWorldTyCon)
                (mkTyConApp ioResTyCon [ Embed (KiVarKi kva), TyVarTy tva ])

{-
The 'IO' tycon has kind
type IO : ∀ k kf. k -> kf
where 'kf' is the kind of the function 'RealWorld -kf> IORes a' and 'a : k'

The 'MkIO' datacon has type
data MkIO : /\k kf -> ∀ {a : k}. PrimIO {k} {kf} a -> IO {k} {kf} a

The 'MkIO' datacon can be thought of as the function
data MkIO = /\ k kf -> /\ {a : k} -> \ (fn : PrimIO {k} {kf} a) -> fn
-}

ioTyConName :: Name
ioTyConName
  = mkWiredInTyConName UserSyntax cSLASH_BUILTIN
    (fsLit "IO") ioTyConKey ioTyCon

mkIoDataConName :: Name
mkIoDataConName
  = mkWiredInDataConName UserSyntax cSLASH_BUILTIN
    (fsLit "MkIO") mkIoDataConKey mkIoDataCon

ioTyCon :: PTyCon
ioTyCon
  = mkAlgTyCon ioTyConName kind arity (mkDataTyConRhs [mkIoDataCon]) VanillaAlgTyCon
  where
    arity = 1

    (kva, kvb) = case mkTemplateKindVars 2 of
                   [k1, k2] -> (k1, k2)
                   _ -> panic "unreachable"

    kind = ForAllKi kva $
           ForAllKi kvb $
           Mono $ FunKi FKF_K_K (KiVarKi kva) (KiVarKi kvb)

mkIoDataCon :: PDataCon
mkIoDataCon = data_con
  where
    tag_map = mkTyConTagMap ioTyCon
    data_con = mkDataCon mkIoDataConName
                         False
                         ioTyCon
                         (lookupNameEnv_NF tag_map mkIoDataConName)
                         (mkDataConId name data_con)
                         dc_ty
                         2
    name = mkDataConName data_con mkIoDataConKey
    dc_ty = let (kva, kvb) = case mkTemplateKindVars 2 of
                               [k1, k2] -> (k1, k2)
                               _ -> panic "unreachable"
                ka = KiVarKi kva
                kb = KiVarKi kvb

                va = case mkTemplateTyVars [ka] of
                       [a] -> a
                       _ -> panic "unreachable"
                a = TyVarTy va

                dc_type = BigTyLamTy kva $
                          BigTyLamTy kvb $
                          ForAllTy (Bndr va Specified) $
                          FunTy (BIKi UKd)
                                (mkTyConApp primIoTyCon [Embed ka, Embed kb, a])
                                (mkTyConApp ioTyCon [Embed ka, Embed kb, a])
            in dc_type
