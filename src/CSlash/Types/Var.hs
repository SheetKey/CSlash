{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiWayIf #-}

module CSlash.Types.Var
  {-( Var, Id
  , TypeVar, KindVar, TcTyVar, TcKiVar, TcVar

  , varName, varUnique, varType, varTypeMaybe, varKind, varKindMaybe
  -- , varMult, varMultMaybe
  , updateVarKind

  , setVarName, setVarUnique

  , mkGlobalVar

  , isTypeVar, isTyVar, isTcTyVar, isKiVar, isTcKiVar

  , ForAllTyFlag(..)
  , isVisibleForAllTyFlag, isInvisibleForAllTyFlag

  , VarBndr(..), ForAllTyBinder, TyVarBinder
  , binderVar, binderVars
  , mkTyVarBinder, mkTyVarBinders

  , ExportFlag(..)

  , mkTyVar, mkTcTyVar, mkKiVar, mkTcKiVar

  , tyVarName, tyVarKind, tcTyVarDetails
  , kiVarName, tcKiVarDetails, setTcKiVarDetails

  , setTyVarName, setTyVarKind

  , nonDetCmpVar
  )-} where

import Prelude hiding ((<>))

import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import {-# SOURCE #-} CSlash.Core.Kind (Kind, pprKind)
import {-# SOURCE #-} CSlash.Tc.Utils.TcType
  (TcTyVarDetails, TcKiVarDetails, pprTcTyVarDetails, vanillaSkolemTvUnk, vanillaSkolemKvUnk)
import {-# SOURCE #-} CSlash.Types.Id.Info (IdDetails, IdInfo, pprIdDetails)

import CSlash.Types.Name hiding (varName)
import CSlash.Types.Unique ( Uniquable, Unique, getKey, getUnique, nonDetCmpUnique )

import CSlash.Utils.Misc
import CSlash.Utils.Binary
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Data.Data
import Control.DeepSeq

type Id = Var

type TypeVar = Var

type KindVar = Var

type TcTyVar = Var

type TcKiVar = Var

type TcVar = Var -- a TcTyVar or TcKiVar

data Var
  = TyVar
    { varName :: !Name
    , realUnique :: {-# UNPACK #-} !Unique
    , varKind :: Kind
    }
  | KdVar
    { varName :: !Name
    , realUnique :: {-# UNPACK #-} !Unique
    }
  | TcTyVar -- for type inference
    { varName :: !Name
    , realUnique :: {-# UNPACK #-} !Unique
    , varKind :: Kind
    , tc_tv_details :: TcTyVarDetails
    }
  | TcKiVar -- for kind inference
    { varName :: !Name
    , realUnique :: {-# UNPACK #-} !Unique
    , tc_kv_details :: TcKiVarDetails
    }
  | Id
    { varName :: !Name
    , realUnique :: {-# UNPACK #-} !Unique
    , varType :: Type
    -- , varMult :: Mult
    , idScope :: IdScope
    , id_details :: IdDetails
    , id_info :: IdInfo
    }

data IdScope
  = GlobalId
  | LocalId ExportFlag

data ExportFlag
  = NotExported
  | Exported

instance Outputable Var where
  ppr var = 
    getPprDebug $ \ debug ->
    getPprStyle $ \ sty ->
    let ppr_var = case var of
          (TyVar {}) | debug -> brackets (text "tv")
          (KdVar {}) | debug -> brackets (text "kv")
          (TcTyVar {tc_tv_details = d})
            | dumpStyle sty || debug
            -> brackets (pprTcTyVarDetails d)
          (Id {idScope = s, id_details = d})
            | debug
            -> brackets (ppr_id_scope s <> pprIdDetails d)
          _ -> empty
    in if | debug
            -> parens (ppr (varName var) -- <+> ppr (varMultMaybe var)
                                         <+> ppr_var <+>
                       colon <+> ppr (varKindMaybe var))
          | otherwise -> ppr (varName var) <> ppr_var
    
ppr_id_scope :: IdScope -> SDoc
ppr_id_scope GlobalId = text "gid"
ppr_id_scope (LocalId Exported) = text "lidx"
ppr_id_scope (LocalId NotExported) = text "lid"

instance NamedThing Var where
  getName = varName

instance Uniquable Var where
  getUnique = varUnique

instance Eq Var where
  a == b = realUnique a == realUnique b

instance Ord Var where
  a <= b = getKey (realUnique a) <= getKey (realUnique b)
  a < b = getKey (realUnique a) < getKey (realUnique b)
  a >= b = getKey (realUnique a) >= getKey (realUnique b)
  a > b = getKey (realUnique a) > getKey (realUnique b)
  a `compare` b = a `nonDetCmpVar` b

nonDetCmpVar :: Var -> Var -> Ordering
nonDetCmpVar a b = varUnique a `nonDetCmpUnique` varUnique b

instance Data Var where
  toConstr _ = abstractConstr "Var"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "Var"

instance HasOccName Var where
  occName = nameOccName . varName

varUnique :: Var -> Unique
varUnique var = realUnique var

-- varMultMaybe :: Id -> Maybe Mult
-- varMultMaybe (Id { varMult = mult }) = Just mult
-- varMultMaybe _ = Nothing

varTypeMaybe :: Id -> Maybe Type
varTypeMaybe (Id { varType = ty }) = Just ty
varTypeMaybe _ = Nothing

varKindMaybe :: Id -> Maybe Kind
varKindMaybe (TyVar { varKind = kd }) = Just kd
varKindMaybe (TcTyVar { varKind = kd }) = Just kd
varKindMaybe _ = Nothing

setVarUnique :: Var -> Unique -> Var
setVarUnique var uniq = var { realUnique = uniq
                            , varName = setNameUnique (varName var) uniq }

setVarName :: Var -> Name -> Var
setVarName var new_name = var { realUnique = getUnique new_name
                              , varName = new_name }

updateVarKind :: (Kind -> Kind) -> Var -> Var
updateVarKind upd var = var { varKind = upd (varKind var) }

updateVarKindSafe :: (Kind -> Kind) -> Var -> Var
updateVarKindSafe upd var
  | isTyVar var = var { varKind = upd (varKind var) }
  | otherwise = var

{- *********************************************************************
*                                                                      *
*                   ForAllTyFlag
*                                                                      *
********************************************************************* -}

data ForAllTyFlag
  = Specified -- type application is optional at call sight
  | Required  -- type application is required at call sight
  deriving (Eq, Ord, Data)

isVisibleForAllTyFlag :: ForAllTyFlag -> Bool
isVisibleForAllTyFlag af = not (isInvisibleForAllTyFlag af)

isInvisibleForAllTyFlag :: ForAllTyFlag -> Bool
isInvisibleForAllTyFlag Specified = True
isInvisibleForAllTyFlag Required = False

instance Outputable ForAllTyFlag where
  ppr Required  = text "[req]"
  ppr Specified = text "[spec]"

instance Binary ForAllTyFlag where
  put_ bh Required  = putByte bh 0
  put_ bh Specified = putByte bh 1

  get bh = do
    h <- getByte bh
    case h of
      0 -> return Required
      _ -> return Specified

{- *********************************************************************
*                                                                      *
*                   FunTyFlag
*                                                                      *
********************************************************************* -}

-- data FunTyFlag
--   = FTF_T_T
--   deriving (Eq, Ord, Data)

-- instance Outputable FunTyFlag where
--   ppr FTF_T_T = text "[->]"

-- instance Binary FunTyFlag where
--   put_ bh FTF_T_T = putByte bh 0

--   get bh = do
--     h <- getByte bh
--     case h of
--       _ -> return FTF_T_T

{- *********************************************************************
*                                                                      *
*                   VarBndr, ForAllTyBinder
*                                                                      *
********************************************************************* -}

data VarBndr var argf = Bndr var argf
  deriving (Data)

type ForAllTyBinder = VarBndr TypeVar ForAllTyFlag
type TyVarBinder = VarBndr TypeVar ForAllTyFlag

binderVar :: VarBndr tv arg -> tv
binderVar (Bndr v _) = v

binderVars :: [VarBndr tv argf] -> [tv]
binderVars tvbs = map binderVar tvbs

isTyVarBinder :: VarBndr TypeVar argf -> Bool
isTyVarBinder (Bndr v _) = isTyVar v

mkTyVarBinder :: vis -> TypeVar -> VarBndr TypeVar vis
mkTyVarBinder vis var
  = assert (isTyVar var) $
    Bndr var vis

mkTyVarBinders :: vis -> [TypeVar] -> [VarBndr TypeVar vis]
mkTyVarBinders vis = map (mkTyVarBinder vis)

instance Outputable tv => Outputable (VarBndr tv ForAllTyFlag) where
  ppr (Bndr v Required) = ppr v
  ppr (Bndr v Specified) = ppr v

instance (Binary tv, Binary vis) => Binary (VarBndr tv vis) where
  put_ bh (Bndr tv vis) = do { put_ bh tv; put_ bh vis }

  get bh = do { tv <- get bh; vis <- get bh; return (Bndr tv vis) }

instance NamedThing tv => NamedThing (VarBndr tv flag) where
  getName (Bndr tv _) = getName tv

{- *********************************************************************
*                                                                      *
*                 Type and kind variables                              *
*                                                                      *
********************************************************************* -}

tyVarName :: TypeVar -> Name
tyVarName = varName

kiVarName :: KindVar -> Name
kiVarName = varName

tyVarKind :: TypeVar -> Kind
tyVarKind = varKind

setTyVarName :: TypeVar -> Name -> TypeVar
setTyVarName = setVarName

setTyVarKind :: TypeVar -> Kind -> TypeVar
setTyVarKind tv k = tv { varKind = k }

updateTyVarKindM :: Monad m => (Kind -> m Kind) -> TypeVar -> m TypeVar
updateTyVarKindM update tv = do
  k' <- update (tyVarKind tv)
  return $ tv { varKind = k' }

mkTyVar :: Name -> Kind -> TypeVar
mkTyVar name kind = TyVar { varName = name
                          , realUnique = nameUnique name
                          , varKind = kind
                          }

mkTcTyVar :: Name -> Kind -> TcTyVarDetails -> TcTyVar
mkTcTyVar name kind details = TcTyVar { varName = name
                                      , realUnique = nameUnique name
                                      , varKind = kind
                                      , tc_tv_details = details }

mkKiVar :: Name -> KindVar
mkKiVar name = KdVar { varName = name, realUnique = nameUnique name }

mkTcKiVar :: Name -> TcKiVarDetails -> TcKiVar
mkTcKiVar name details
  = TcKiVar { varName = name
            , realUnique = nameUnique name
            , tc_kv_details = details }

tcTyVarDetails :: TypeVar -> TcTyVarDetails
tcTyVarDetails (TcTyVar { tc_tv_details = details }) = details
tcTyVarDetails (TyVar {}) = vanillaSkolemTvUnk
tcTyVarDetails var
  = pprPanic "tcTyVarDetails" (ppr var <+> colon <+> ppr (varKindMaybe var))

tcKiVarDetails :: KindVar -> TcKiVarDetails
tcKiVarDetails (TcKiVar { tc_kv_details = details }) = details
tcKiVarDetails (KdVar {}) = vanillaSkolemKvUnk
tcKiVarDetails var = pprPanic "tcKiVarDetails" (ppr var)

setTcKiVarDetails :: KindVar -> TcKiVarDetails -> KindVar
setTcKiVarDetails kv details = kv { tc_kv_details = details }

{- *********************************************************************
*                                                                      *
            Ids
*                                                                      *
********************************************************************* -}

mkGlobalVar :: IdDetails -> Name -> Type -> IdInfo -> Id
mkGlobalVar details name ty info
  = mk_id name ty GlobalId details info

mk_id :: Name -> Type -> IdScope -> IdDetails -> IdInfo -> Id
mk_id name ty scope details info
  = Id { varName = name
       , realUnique = nameUnique name
       , varType = ty
       , idScope = scope
       , id_details = details
       , id_info = info
       }

{- *********************************************************************
*                                                                      *
            Predicates over variables
*                                                                      *
********************************************************************* -}

isTypeVar :: Var -> Bool
isTypeVar (TyVar {}) = True
isTypeVar _ = False

isTyVar :: Var -> Bool
isTyVar (TyVar {}) = True
isTyVar (TcTyVar {}) = True
isTyVar _ = False

isTcTyVar :: Var -> Bool
isTcTyVar (TcTyVar {}) = True
isTcTyVar _ = False

isKiVar :: Var -> Bool
isKiVar (KdVar {}) = True
isKiVar (TcKiVar {}) = True
isKiVar _ = False

isTcKiVar :: Var -> Bool
isTcKiVar (TcKiVar {}) = True
isTcKiVar _ = False
