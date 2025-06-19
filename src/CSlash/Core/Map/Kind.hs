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
  { km_var :: VarMap AnyKiVar a
  , km_kicon :: DKiConEnv a
  }

instance Functor KindMapX where
  fmap f KM {..} = KM { km_var = fmap f km_var
                      , km_kicon = fmap f km_kicon
                      }

instance TrieMap KindMapX where
  type Key KindMapX = MonoKind AnyKiVar
  emptyTM = emptyK
  lookupTM = lkK
  alterTM = xtK
  foldTM = fdK
  filterTM = filterK

emptyK :: KindMapX a
emptyK = KM { km_var = emptyTM
            , km_kicon = emptyUDFM }

lkK :: MonoKind AnyKiVar -> KindMapX a -> Maybe a
lkK (KiVarKi v) = km_var >.> lkVar v
lkK (KiConApp kc []) = km_kicon >.> lkDKiCon kc
lkK ki@(KiConApp {}) = pprPanic "lkK KiConApp" (ppr ki)
lkK ki@(FunKi {}) = pprPanic "lkK FunKi" (ppr ki)

xtK :: MonoKind AnyKiVar -> XT a -> KindMapX a -> KindMapX a
xtK (KiVarKi v) f m = m { km_var = km_var m |> xtVar v f }
xtK (KiConApp kc []) f m = m { km_kicon = km_kicon m |> xtDKiCon kc f }
xtK ki@(KiConApp {}) _ _ = pprPanic "xtK KiConApp" (ppr ki)
xtK ki@(FunKi {}) _ _ = pprPanic "xtK FunKi" (ppr ki)

fdK :: (a -> b -> b) -> KindMapX a -> b -> b
fdK k m = foldTM k (km_var m)
        . foldTM k (km_kicon m)

filterK :: (a -> Bool) -> KindMapX a -> KindMapX a
filterK f (KM { km_var = kvar, km_kicon = kkicon })
  = KM { km_var = filterTM f kvar
       , km_kicon = filterTM f kkicon }

{- *********************************************************************
*                                                                      *
                   Variables
*                                                                      *
********************************************************************* -}

data VarMap v a = VM { vm_fvar :: MkDVarEnv v a }

instance Functor (VarMap v) where
  fmap f VM { vm_fvar = fv } = VM { vm_fvar = fmap f fv }

instance IsVar v => TrieMap (VarMap v) where
   type Key (VarMap v) = v
   emptyTM  = VM { vm_fvar = emptyDVarEnv }
   lookupTM = lkVar 
   alterTM  = xtVar 
   foldTM   = fdVar
   filterTM = ftVar

lkVar :: IsVar v => v -> VarMap v a -> Maybe a
lkVar v = vm_fvar >.> lkDFreeVar v

xtVar :: IsVar v => v -> XT a -> VarMap v a -> VarMap v a
xtVar v f m = m { vm_fvar = vm_fvar m |> xtDFreeVar v f }

fdVar :: IsVar v => (a -> b -> b) -> VarMap v a -> b -> b
fdVar k m = foldTM k (vm_fvar m)

lkDFreeVar :: IsVar v => v -> MkDVarEnv v a -> Maybe a
lkDFreeVar var env = lookupDVarEnv env var

xtDFreeVar :: IsVar v => v -> XT a -> MkDVarEnv v a -> MkDVarEnv v a
xtDFreeVar v f m = alterDVarEnv f m v

ftVar :: IsVar v => (a -> Bool) -> VarMap v a -> VarMap v a
ftVar f (VM { vm_fvar = fv }) = VM { vm_fvar = filterTM f fv }

lkDKiCon :: KiCon -> DKiConEnv a -> Maybe a
lkDKiCon kc env = lookupDKiConEnv env kc

xtDKiCon :: KiCon -> XT a -> DKiConEnv a -> DKiConEnv a
xtDKiCon kc f m = alterDKiConEnv f m kc
