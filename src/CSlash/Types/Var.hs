{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiWayIf #-}

module CSlash.Types.Var
  ( Var, Id
  , TypeVar, KindVar, TcTyVar

  , varName, varUnique, varType, varTypeMaybe, varKind, varKindMaybe
  -- , varMult, varMultMaybe

  , setVarName, setVarUnique

  , mkGlobalVar

  , isTyVar, isKdVar

  , ForAllTyFlag(..)

  , VarBndr(..), ForAllTyBinder, TyVarBinder
  , binderVar, binderVars
  , mkTyVarBinder, mkTyVarBinders

  , ExportFlag(..)

  , mkTyVar, mkKdVar

  , tyVarName

  , setTyVarKind

  , nonDetCmpVar
  ) where

import Prelude hiding ((<>))

import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import {-# SOURCE #-} CSlash.Core.Kind (Kind, pprKind)
import {-# SOURCE #-} CSlash.Tc.Utils.TcType (TcTyVarDetails, pprTcTyVarDetails)
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
  ppr var = sdocOption sdocSuppressVarKinds $ \ supp_var_kinds ->
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
    in if | debug && (not supp_var_kinds)
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

{- *********************************************************************
*                                                                      *
*                   ForAllTyFlag
*                                                                      *
********************************************************************* -}

data ForAllTyFlag
  = Specified -- type application is optional at call sight
  | Required  -- type application is required at call sight
  deriving (Eq, Ord, Data)

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

mkTyVarBinder :: vis -> TypeVar -> VarBndr TypeVar vis
mkTyVarBinder vis var
  = assert (isTyVar var) $
    Bndr var vis

mkTyVarBinders :: vis -> [TypeVar] -> [VarBndr TypeVar vis]
mkTyVarBinders vis = map (mkTyVarBinder vis)

{- *********************************************************************
*                                                                      *
*                 Type and kind variables                              *
*                                                                      *
********************************************************************* -}

tyVarName :: TypeVar -> Name
tyVarName = varName

setTyVarKind :: TypeVar -> Kind -> TypeVar
setTyVarKind tv k = tv { varKind = k }

mkTyVar :: Name -> Kind -> TypeVar
mkTyVar name kind = TyVar { varName = name
                          , realUnique = nameUnique name
                          , varKind = kind
                          }

mkKdVar :: Name -> KindVar
mkKdVar name = KdVar { varName = name, realUnique = nameUnique name }

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

isTyVar :: Var -> Bool
isTyVar (TyVar {}) = True
isTyVar (TcTyVar {}) = True
isTyVar _ = False

isKdVar :: Var -> Bool
isKdVar (KdVar {}) = True
isKdVar _ = False
