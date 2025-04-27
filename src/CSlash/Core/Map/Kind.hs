{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecordWildCards #-}

module CSlash.Core.Map.Kind where

import CSlash.Core.Kind
import CSlash.Data.TrieMap

import CSlash.Data.FastString
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.DFM
import CSlash.Utils.Outputable

import CSlash.Utils.Panic

import qualified Data.Map    as Map
import qualified Data.IntMap as IntMap

import Control.Monad ( (>=>) )

{- *********************************************************************
*                                                                      *
                   Types
*                                                                      *
********************************************************************* -}

type KindMap = GenMap KindMapX

data KindMapX a = KM
  { km_var :: VarMap a
  , km_kicon :: DKiConEnv a
  }

instance Functor KindMapX where
  fmap f KM {..} = KM { km_var = fmap f km_var
                      , km_kicon = fmap f km_kicon
                      }

instance TrieMap KindMapX where
  type Key KindMapX = MonoKind
  emptyTM = emptyK
  lookupTM = lkK
  alterTM = xtK
  foldTM = fdK
  filterTM = filterK

emptyK :: KindMapX a
emptyK = KM { km_var = emptyTM
            , km_kicon = emptyUDFM }

lkK :: MonoKind -> KindMapX a -> Maybe a
lkK ki m = panic "lkK"

xtK :: MonoKind -> XT a -> KindMapX a -> KindMapX a
xtK ki f m = panic "xtK"

fdK :: (a -> b -> b) -> KindMapX a -> b -> b
fdK k m b = panic "fdK"

filterK :: (a -> Bool) -> KindMapX a -> KindMapX a
filterK f km = panic "filterK"

{- *********************************************************************
*                                                                      *
                   Variables
*                                                                      *
********************************************************************* -}

data VarMap a = VM { vm_fvar :: DVarEnv a }

instance Functor VarMap where
  fmap f VM { vm_fvar = fv } = VM { vm_fvar = fmap f fv }

instance TrieMap VarMap where
   type Key VarMap = Var
   emptyTM  = VM { vm_fvar = emptyDVarEnv }
   lookupTM = lkVar 
   alterTM  = xtVar 
   foldTM   = fdVar
   filterTM = ftVar

lkVar :: Var -> VarMap a -> Maybe a
lkVar v = vm_fvar >.> lkDFreeVar v

xtVar :: Var -> XT a -> VarMap a -> VarMap a
xtVar v f m = m { vm_fvar = vm_fvar m |> xtDFreeVar v f }

fdVar :: (a -> b -> b) -> VarMap a -> b -> b
fdVar k m = foldTM k (vm_fvar m)

lkDFreeVar :: Var -> DVarEnv a -> Maybe a
lkDFreeVar var env = lookupDVarEnv env var

xtDFreeVar :: Var -> XT a -> DVarEnv a -> DVarEnv a
xtDFreeVar v f m = alterDVarEnv f m v

ftVar :: (a -> Bool) -> VarMap a -> VarMap a
ftVar f (VM { vm_fvar = fv }) = VM { vm_fvar = filterTM f fv }
