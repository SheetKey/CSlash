{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}

module CSlash.Iface.Type where

import Prelude hiding ((<>))

import {-# SOURCE #-} CSlash.Builtin.Types
  ( tupleTyConName
  , tupleDataConName
  , sumTyCon )
-- import GHC.Core.Type ( isRuntimeRepTy, isMultiplicityTy, isLevityTy, funTyFlagTyCon )
import CSlash.Core.Kind (FunKiFlag)
-- import GHC.Core.TyCo.Rep( CoSel )
-- import GHC.Core.TyCo.Compare( eqForAllVis )
import CSlash.Core.TyCon
-- import GHC.Core.Coercion.Axiom
import CSlash.Types.Var
import CSlash.Builtin.Names
-- import {-# SOURCE #-} GHC.Builtin.Types ( liftedTypeKindTyConName )
import CSlash.Types.Name
import CSlash.Types.Basic
import CSlash.Utils.Binary
import CSlash.Utils.Outputable
import CSlash.Data.FastString
import CSlash.Utils.Misc
import CSlash.Utils.Panic
-- import {-# SOURCE #-} GHC.Tc.Utils.TcType ( isMetaTyVar, isTyConableTyVar )

import Data.Maybe( isJust )
import qualified Data.Semigroup as Semi
import Control.DeepSeq

{- *********************************************************************
*                                                                      *
                Local (nested) binders
*                                                                      *
********************************************************************* -}

type IfLclName = FastString

type IfExtName = Name

data IfaceBndr
  = IfaceIdBndr {-# UNPACK #-} !IfaceIdBndr
  | IfaceTvBndr {-# UNPACK #-} !IfaceTvBndr

type IfaceIdBndr = (IfaceType, IfLclName, IfaceType)

type IfaceTvBndr = (IfLclName, IfaceKind)

{- **********************************************************************
*                                                                       *
                IfaceKind
*                                                                       *
********************************************************************** -}

data IfaceKind
  = IfaceKiVar IfLclName
  | IfaceUKd
  | IfaceAKd
  | IfaceLKd
  | IfaceFunKi FunKiFlag IfaceKind IfaceKind
  | IfaceKdContext [IfaceKdRel]

data IfaceKdRel

{- **********************************************************************
*                                                                       *
                IfaceType
*                                                                       *
********************************************************************** -}

data IfaceType
  = IfaceFreeTyVar (TyVar KiVar)
  | IfaceTyVar IfLclName
  | IfaceAppTy IfaceType IfaceAppArgs
  | IfaceFunTy IfaceKind IfaceType IfaceType
  | IfaceForAllTy IfaceForAllBndr IfaceType
  | IfaceTyConApp IfaceTyCon IfaceAppArgs
  | IfaceTupleTy IfaceAppArgs
  | IfaceWithContext IfaceKind IfaceType

type IfaceTyConBinder = VarBndr IfaceBndr ForAllFlag
type IfaceForAllBndr = VarBndr IfaceBndr ForAllFlag

data IfaceAppArgs
  = IA_Nil
  | IA_Arg IfaceType ForAllFlag IfaceAppArgs

instance Semi.Semigroup IfaceAppArgs where
  IA_Nil <> xs = xs
  IA_Arg ty argf rest <> xs = IA_Arg ty argf (rest Semi.<> xs)

instance Monoid IfaceAppArgs where
  mempty = IA_Nil
  mappend = (Semi.<>)

data IfaceTyCon = IfaceTyCon
  { ifaceTyConName :: IfExtName
  , ifaceTyConInfo :: IfaceTyConInfo
  }
  deriving (Eq)

data IfaceTyConSort
  = IfaceNormalTyCon
  | IfaceTupleTyCon !Arity
  | IfaceSumTyCon !Arity
  deriving (Eq)

instance Outputable IfaceTyConSort where
  ppr IfaceNormalTyCon = text "normal"
  ppr (IfaceTupleTyCon n) = text "tuple:" <> ppr n
  ppr (IfaceSumTyCon n) = text "sum:" <> ppr n

data IfaceTyConInfo = IfaceTyConInfo { ifaceTyConSort :: IfaceTyConSort }
  deriving (Eq)

mkIfaceTyConInfo :: IfaceTyConSort -> IfaceTyConInfo
mkIfaceTyConInfo IfaceNormalTyCon = IfaceTyConInfo IfaceNormalTyCon
mkIfaceTyConInfo sort = IfaceTyConInfo sort

{- *********************************************************************
*                                                                      *
                Functions over IfaceTypes
*                                                                      *
********************************************************************* -}

ifaceTyConHasKey :: IfaceTyCon -> Unique -> Bool
ifaceTyConHasKey tc key = ifaceTyConName tc `hasKey` key

-- deliberately different from GHC: we handle vis/invis differently
splitIfaceSigmaTy :: IfaceType -> ([IfaceForAllBndr], IfaceType)
splitIfaceSigmaTy ty
  = case bndrs of
      [] -> (bndrs, tau)
      _ -> let (bndrs', tau') = splitIfaceSigmaTy tau
           in (bndrs ++ bndrs', tau')
  where
    (bndrs, tau) = split_foralls ty

    split_foralls (IfaceForAllTy bndr ty)
      = case split_foralls ty of
          (bndrs, tau) -> (bndr:bndrs, tau)
    split_foralls tau = ([], tau)

{- *********************************************************************
*                                                                      *
                Functions over IfaceAppArgs
*                                                                      *
********************************************************************* -}

appArgsIfaceTypes :: IfaceAppArgs -> [IfaceType]
appArgsIfaceTypes IA_Nil = []
appArgsIfaceTypes (IA_Arg t _ ts) = t : appArgsIfaceTypes ts

appArgsIfaceTypesForAllTyFlags :: IfaceAppArgs -> [(IfaceType, ForAllFlag)]
appArgsIfaceTypesForAllTyFlags IA_Nil = []
appArgsIfaceTypesForAllTyFlags (IA_Arg t a ts)
  = (t, a) : appArgsIfaceTypesForAllTyFlags ts

ifaceVisAppArgsLength :: IfaceAppArgs -> Int
ifaceVisAppArgsLength = go 0
  where
    go !n IA_Nil = n
    go n (IA_Arg _ argf rest)
      | isVisibleForAllFlag argf = go (n+1) rest
      | otherwise = go n rest

{- *********************************************************************
*                                                                      *
                Pretty-printing
*                                                                      *
********************************************************************* -}

pprIfaceInfixApp :: PprPrec -> SDoc -> SDoc -> SDoc -> SDoc
pprIfaceInfixApp ctxt_prec pp_tc pp_ty1 pp_ty2
  = maybeParen ctxt_prec opPrec $
    sep [pp_ty1, pp_tc <+> pp_ty2]

pprIfacePrefixApp :: PprPrec -> SDoc -> [SDoc] -> SDoc
pprIfacePrefixApp ctxt_prec pp_fun pp_tys
  | null pp_tys = pp_fun
  | otherwise = maybeParen ctxt_prec appPrec $
                hang pp_fun 2 (sep pp_tys)

isIfaceRhoType :: IfaceType -> Bool
isIfaceRhoType (IfaceForAllTy _ _) = False
isIfaceRhoType (IfaceWithContext _ ty) = isIfaceRhoType ty
isIfaceRhoType _ = True

instance Outputable IfaceBndr where
  ppr (IfaceIdBndr bndr) = pprIfaceIdBndr bndr
  ppr (IfaceTvBndr bndr) = pprIfaceTvBndr bndr (SuppressBndrSig False) (UseBndrParens False)

pprIfaceBndrs :: [IfaceBndr] -> SDoc
pprIfaceBndrs bs = sep (map ppr bs)

pprIfaceIdBndr :: IfaceIdBndr -> SDoc
pprIfaceIdBndr (w, name, ty) = parens (ppr name <> brackets (ppr_ty_nested w)
                                       <+> colon <+> ppr_ty_nested ty)

newtype SuppressBndrSig = SuppressBndrSig Bool

newtype UseBndrParens = UseBndrParens Bool

pprIfaceTvBndr :: IfaceTvBndr -> SuppressBndrSig -> UseBndrParens -> SDoc
pprIfaceTvBndr (tv, kd) (SuppressBndrSig suppress_sig) (UseBndrParens use_parens)
  | suppress_sig = ppr tv
  | otherwise = maybe_parens (ppr tv <+> colon <+> ppr_kd_nested kd)
  where
    maybe_parens | use_parens = parens
                 | otherwise = id

putIfaceType :: WriteBinHandle -> IfaceType -> IO ()
putIfaceType = panic "putIfaceType"

instance Binary IfaceBndr where
  put_ bh (IfaceIdBndr aa) = do
    putByte bh 0
    put_ bh aa
  put_ bh (IfaceTvBndr ab) = do
    putByte bh 1
    put_ bh ab
  get bh = do
    h <- getByte bh
    case h of
      0 -> do aa <- get bh
              return (IfaceIdBndr aa)
      _ -> do ab <- get bh
              return (IfaceTvBndr ab)

instance Outputable IfaceType where
  ppr ty = pprIfaceType ty

pprIfaceType :: IfaceType -> SDoc
pprIfaceType = pprPrecIfaceType topPrec

ppr_ty_nested :: IfaceType -> SDoc
ppr_ty_nested = ppr_ty topPrec

ppr_kd_nested :: IfaceKind -> SDoc
ppr_kd_nested = ppr_kd topPrec

pprPrecIfaceType :: PprPrec -> IfaceType -> SDoc
pprPrecIfaceType prec ty = ppr_ty prec ty

pprTypeArrow :: IfaceKind -> SDoc
pprTypeArrow IfaceLKd = linarrow
pprTypeArrow IfaceAKd = affarrow
pprTypeArrow IfaceUKd = unrarrow
pprTypeArrow (IfaceKiVar kv) = char '-' <> ppr kv <> char '>'
pprTypeArrow _ = panic "pprTypeArrow"

ppr_ty :: PprPrec -> IfaceType -> SDoc
ppr_ty ctxt_prec ty
  | not (isIfaceRhoType ty) = ppr_sigma ctxt_prec ty
ppr_ty _ (IfaceForAllTy {}) = panic "ppr_ty"
ppr_ty _ (IfaceFreeTyVar tyvar) = ppr tyvar
ppr_ty _ (IfaceTyVar tyvar) = ppr tyvar
ppr_ty ctxt_prec (IfaceTyConApp tc tys) = pprTyTcApp ctxt_prec tc tys
ppr_ty ctxt_prec (IfaceTupleTy tys) = ppr_tuple ctxt_prec tys
ppr_ty _ (IfaceWithContext kd ty) = ppr_with_context kd ty
ppr_ty ctxt_prec (IfaceFunTy kd ty1 ty2)
  = maybeParen ctxt_prec funPrec $
    sep [ppr_ty funPrec ty1, sep (ppr_fun_tail kd ty2)]
  where
    ppr_fun_tail kd (IfaceFunTy kd2 ty1 ty2)
      = (pprTypeArrow kd <+> ppr_ty funPrec ty1) : ppr_fun_tail kd2 ty2
    ppr_fun_tail kd ty = [pprTypeArrow kd <+> ppr_ty_nested ty]
ppr_ty ctxt_prec (IfaceAppTy t ts)
  = let tys = appArgsIfaceTypesForAllTyFlags ts
    in pprIfacePrefixApp ctxt_prec (ppr_ty funPrec t) (map (ppr_app_arg appPrec) tys)

ppr_kd :: PprPrec -> IfaceKind -> SDoc
ppr_kd = undefined

ppr_with_context = undefined

instance Outputable IfaceAppArgs where
  ppr tcs = pprIfaceAppArgs tcs

pprIfaceAppArgs :: IfaceAppArgs -> SDoc
pprIfaceAppArgs = ppr_app_args topPrec

ppr_app_args :: PprPrec -> IfaceAppArgs -> SDoc
ppr_app_args ctx_prec = go
  where
    go :: IfaceAppArgs -> SDoc
    go IA_Nil = empty
    go (IA_Arg t argf ts) = ppr_app_arg ctx_prec (t, argf) <+> go ts

ppr_app_arg :: PprPrec -> (IfaceType, ForAllFlag) -> SDoc
ppr_app_arg ctx_prec (t, argf) =
  case argf of
    Required -> ppr_ty ctx_prec t
    Specified -> ppr_ty ctx_prec t
    Inferred -> braces (ppr_ty_nested t)

pprIfaceForAll :: [IfaceForAllBndr] -> SDoc
pprIfaceForAll [] = empty
pprIfaceForAll bndrs
  = forAllLit <+> sep (pprIfaceForAllBndr <$> bndrs) <> dot

pprIfaceForAllBndr :: IfaceForAllBndr -> SDoc
pprIfaceForAllBndr bndr =
  case bndr of
    Bndr (IfaceTvBndr tv) Required ->
      pprIfaceTvBndr tv suppress_sig (UseBndrParens True)
    Bndr (IfaceTvBndr tv) Specified ->
      braces $ pprIfaceTvBndr tv suppress_sig (UseBndrParens False)
    Bndr (IfaceTvBndr tv) Inferred ->
      braces $ pprIfaceTvBndr tv suppress_sig (UseBndrParens False)
    Bndr (IfaceIdBndr _) _ -> panic "pprIfaceForAllBndr"
  where
    suppress_sig = SuppressBndrSig False

newtype ShowSub = ShowSub { ss_how_much :: ShowHowMuch }

newtype AltPpr = AltPpr (Maybe (OccName -> SDoc))

data ShowHowMuch
  = ShowHeader AltPpr
  | ShowSome (Maybe (OccName -> Bool)) AltPpr
  | ShowIface

instance Outputable ShowHowMuch where
  ppr (ShowHeader _) = text "ShowHeader"
  ppr ShowIface = text "ShowIface"
  ppr (ShowSome _ _) = text "ShowSome"

ppr_sigma :: PprPrec -> IfaceType -> SDoc
ppr_sigma ctxt_prec iface_ty
  = maybeParen ctxt_prec funPrec $
    let (tvs, tau) = splitIfaceSigmaTy iface_ty
    in sep [pprIfaceForAll tvs, ppr_ty_nested tau]

pprTyTcApp :: PprPrec -> IfaceTyCon -> IfaceAppArgs -> SDoc
pprTyTcApp ctxt_prec tc tys =
  sdocOption sdocPrintTypeAbbreviations $ \print_type_abbreviations ->
  getPprDebug $ \debug ->

  if | IfaceTupleTyCon arity <- ifaceTyConSort info
     , not debug
     , arity == ifaceVisAppArgsLength tys
       -> ppr_tuple ctxt_prec tys

     | IfaceSumTyCon arity <- ifaceTyConSort info
     , not debug
     , arity == ifaceVisAppArgsLength tys
       -> ppr_sum ctxt_prec tys

     | tc `ifaceTyConHasKey` fUNTyConKey
     , print_type_abbreviations
       -> pprIfacePrefixApp ctxt_prec (parens arrow) (map (ppr_app_arg appPrec) $
                                                      appArgsIfaceTypesForAllTyFlags tys)
     | otherwise
       -> ppr_iface_tc_app ppr_app_arg ctxt_prec tc $
          appArgsIfaceTypesForAllTyFlags tys
  where
    info = ifaceTyConInfo tc

ppr_iface_tc_app
  :: (PprPrec -> (a, ForAllFlag) -> SDoc)
  -> PprPrec -> IfaceTyCon -> [(a, ForAllFlag)] -> SDoc
ppr_iface_tc_app pp ctxt_prec tc tys 
  | not (isSymOcc (nameOccName (ifaceTyConName tc)))
  =  pprIfacePrefixApp ctxt_prec (ppr tc) (map (pp appPrec) tys)
  
  | [ ty1@(_, Required), ty2@(_, Required) ] <- tys
  = pprIfaceInfixApp ctxt_prec (ppr tc) (pp opPrec ty1) (pp opPrec ty2)

  | otherwise
  = pprIfacePrefixApp ctxt_prec (parens (ppr tc)) (map (pp appPrec) tys)

data TupleOrSum = IsSum | IsTuple
  deriving Eq

ppr_tuple_sum_pun :: PprPrec -> TupleOrSum -> IfaceType -> Arity -> [IfaceType] -> SDoc
ppr_tuple_sum_pun ctxt_prec IsSum tc arity tys
  = parens (pprWithBars (ppr_ty topPrec) tys)
ppr_tuple_sum_pun ctxt_prec IsTuple tc arity tys
  | arity == 1
  = pprPrecIfaceType ctxt_prec tc
  | otherwise
  = parens (pprWithCommas pprIfaceType tys)

ppr_tuple_sum :: PprPrec -> TupleOrSum -> IfaceAppArgs -> SDoc
ppr_tuple_sum ctxt_prec sort args =
  ppr_tuple_sum_pun ctxt_prec sort prefix_tc arity non_rep_tys
  where
    prefix_tc = IfaceTyConApp (IfaceTyCon (mk_name arity) info) args

    info = mkIfaceTyConInfo IfaceNormalTyCon

    mk_name = case sort of
                IsTuple -> tupleDataConName
                IsSum -> tyConName . sumTyCon

    non_rep_tys = drop arity all_tys

    arity = count `div` 2

    count = length all_tys

    all_tys = appArgsIfaceTypes args

ppr_sum :: PprPrec -> IfaceAppArgs -> SDoc
ppr_sum ctxt_prec = ppr_tuple_sum ctxt_prec IsSum

ppr_tuple :: PprPrec -> IfaceAppArgs -> SDoc
ppr_tuple ctxt_prec = ppr_tuple_sum ctxt_prec IsTuple

instance Outputable IfaceTyCon where
  ppr tc = ppr (ifaceTyConName tc)

instance Outputable IfaceTyConInfo where
  ppr (IfaceTyConInfo { ifaceTyConSort = sort })
    = angleBrackets $ ppr sort

instance Binary IfaceTyCon where
  put_ bh (IfaceTyCon n i) = put_ bh n >> put_ bh i

  get bh = do n <- get bh
              i <- get bh
              return (IfaceTyCon n i)

instance Binary IfaceTyConSort where
  put_ bh IfaceNormalTyCon = putByte bh 0
  put_ bh (IfaceTupleTyCon arity) =  putByte bh 1 >> put_ bh arity
  put_ bh (IfaceSumTyCon arity) = putByte bh 2 >> put_ bh arity

  get bh = do
    n <- getByte bh
    case n of
      0 -> return IfaceNormalTyCon
      1 -> IfaceTupleTyCon <$> get bh
      2 -> IfaceSumTyCon <$> get bh
      _ -> panic "Invalid byte"

instance Binary IfaceTyConInfo where
  put_ bh (IfaceTyConInfo s) = put_ bh s 

  get bh = mkIfaceTyConInfo <$> get bh

instance Binary IfaceAppArgs where
  put_ bh tk =
    case tk of
      IA_Arg t a ts -> putByte bh 0 >> put_ bh t >> put_ bh a >> put_ bh ts
      IA_Nil -> putByte bh 1

  get bh = do
    c <- getByte bh
    case c of
      0 -> do t <- get bh
              a <- get bh
              ts <- get bh
              return $! IA_Arg t a ts
      1 -> return IA_Nil
      _ -> panic ("get IfaceAppArgs " ++ show c)

instance Binary IfaceType where
  put_ _ (IfaceFreeTyVar tv)
    = pprPanic "Can't serialise IfaceFreeTyVar" (ppr tv)
  put_ bh (IfaceForAllTy aa ab) = do
    putByte bh 0
    put_ bh aa
    put_ bh ab
  put_ bh (IfaceTyVar ad) = do
    putByte bh 1
    put_ bh ad
  put_ bh (IfaceAppTy ae af) = do
    putByte bh 2
    put_ bh ae
    put_ bh af
  put_ bh (IfaceFunTy af ag ah) = do
    putByte bh 3
    put_ bh af
    put_ bh ag
    put_ bh ah
  put_ bh (IfaceTyConApp tc tys) = do
    putByte bh 5
    put_ bh tc
    put_ bh tys
  put_ bh (IfaceTupleTy tys) = do
    putByte bh 8
    put_ bh tys
  put_ bh (IfaceWithContext kd ty) = do
    putByte bh 10
    put_ bh kd
    put_ bh ty

  get bh = do
    h <- getByte bh
    case h of
      0 -> do aa <- get bh
              ab <- get bh
              return (IfaceForAllTy aa ab)
      1 -> do ad <- get bh
              return (IfaceTyVar ad)
      2 -> do ae <- get bh
              af <- get bh
              return (IfaceAppTy ae af)
      3 -> do af <- get bh
              ag <- get bh
              ah <- get bh
              return (IfaceFunTy af ag ah)
      5 -> do tc <- get bh
              tys <- get bh
              return (IfaceTyConApp tc tys)
      8 -> do tys <- get bh
              return (IfaceTupleTy tys)
      10 -> do kd <- get bh
               ty <- get bh
               return (IfaceWithContext kd ty)
      _ -> panic "Invalid byte"

instance Binary IfaceKind
