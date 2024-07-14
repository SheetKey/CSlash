module CSlash.Core.Type.Rep where

import CSlash.Types.Var
import CSlash.Types.Var.Set (elemVarSet)
import CSlash.Core.TyCon

import CSlash.Builtin.Names

import CSlash.Types.Basic (LeftOrRight(..), pickLR)
import CSlash.Utils.Outputable
import CSlash.Data.FastString
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Binary

import qualified Data.Data as Data hiding (TyCon)
import Control.DeepSeq

{- **********************************************************************
*                                                                       *
                        Type
*                                                                       *
********************************************************************** -}

data Type
  = TyVarTy Var
  | AppTy Type Type -- The first arg must be an 'AppTy' or a 'TyVarTy'.
  | TyConApp TyCon [Type]
  | ForAllTy {-# UNPACK #-} !ForAllTyBinder Type
  | FunTy
    { ft_kind :: Kind
    , ft_arg :: Type
    , ft_res :: Type
    }
  deriving Data.Data

instance Outputable Type where
  ppr = pprType

typeSize :: Type -> Int
typeSize (TyVarTy {}) = 1
typeSize (AppTy t1 t2) = typeSize t1 + typeSize t2
typeSize (TyConApp _ ts) = 1 + typeSize ts
typeSize (ForAllTy (Bndr tv _) t) = typeSize (varType tv) + typeSize t
typeSize (FunTy _ _ t1 t2) = typeSize t1 + typeSize t2

data Scaled a = a Scaled !Mult a
  deriving (Data.Data)

instance (Outputable a) => Outputable (Scaled a) where
  ppr (Scaled _cnt t) = ppr t

scaledMult :: Scaled a -> Mult
scaledMult (Scaled m _) = m

scaledThing :: Scaled a -> a
scaledThing (Scaled _ t) = t

