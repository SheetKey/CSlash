{-# LANGUAGE FlexibleContexts #-}

module CSlash.Tc.Types.Evidence where

import Prelude hiding ((<>))

import CSlash.Types.Unique.DFM
import CSlash.Types.Unique.FM
import CSlash.Types.Var
-- import GHC.Types.Id( idScaledType )
-- import GHC.Core.Coercion.Axiom
-- import GHC.Core.Coercion
import CSlash.Core.Ppr ()   -- Instance OutputableBndr TyVar
import CSlash.Tc.Utils.TcType
import CSlash.Core.Type
import CSlash.Core.Type.FVs
import CSlash.Core.Kind
import CSlash.Core.TyCon
import CSlash.Core.DataCon ( DataCon{-, dataConWrapId-} )
import CSlash.Builtin.Names
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Core.Predicate
import CSlash.Types.Basic

import CSlash.Core
-- import GHC.Core.Class (Class, classSCSelId )
-- import GHC.Core.FVs   ( exprSomeFreeVars )
-- import GHC.Core.InstEnv ( Canonical )

import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Outputable

import CSlash.Data.Bag
import CSlash.Data.FastString

import qualified Data.Data as Data
import CSlash.Types.SrcLoc
import Data.IORef( IORef )
import CSlash.Types.Unique.Set
-- import GHC.Core.Multiplicity

import qualified Data.Semigroup as S

maybeSymCo :: SwapFlag -> KindCoercion kv -> KindCoercion kv
maybeSymCo IsSwapped co = mkSymKiCo co
maybeSymCo NotSwapped co = co

{- *********************************************************************
*                                                                      *
                  CsWrapper
*                                                                      *
********************************************************************* -}
  
data CsWrapper
  = WpHole
  | WpCompose CsWrapper CsWrapper
  | WpTyLam (AnyTyVar AnyKiVar) -- can probably be 'TcTyVar AnyKiVar' (these should be skols)
  | WpKiLam AnyKiVar            -- "             " 'TcKiVar'          "                     "

(<.>) :: CsWrapper -> CsWrapper -> CsWrapper
WpHole <.> c = c
c <.> WpHole = c
c1 <.> c2 = c1 `WpCompose` c2

idCsWrapper :: CsWrapper
idCsWrapper = WpHole

isIdCsWrapper :: CsWrapper -> Bool
isIdCsWrapper WpHole = True
isIdCsWrapper _ = False

mkWpTyLams :: [AnyTyVar AnyKiVar] -> CsWrapper
mkWpTyLams tvs = mk_lam_fn WpTyLam tvs

mkWpKiLams :: [AnyKiVar] -> CsWrapper
mkWpKiLams kvs = mk_lam_fn WpKiLam kvs

mk_lam_fn :: (a -> CsWrapper) -> [a] -> CsWrapper
mk_lam_fn f as = foldr (\x wrap -> f x <.> wrap) WpHole as

{- *********************************************************************
*                                                                      *
                  Evidence bindings
*                                                                      *
********************************************************************* -}

data KiCoBindsVar
  = KiCoBindsVar
    { kcbv_uniq :: Unique
    , kcbv_kcvs :: IORef (MkVarSet (KiCoVar AnyKiVar))
    }

{- *********************************************************************
*                                                                      *
         Evidence for holes
*                                                                      *
********************************************************************* -}

{- *********************************************************************
*                                                                      *
                  Free variables
*                                                                      *
********************************************************************* -}

{- *********************************************************************
*                                                                      *
                  Pretty printing
*                                                                      *
********************************************************************* -}

instance Outputable KiCoBindsVar where
  ppr (KiCoBindsVar { kcbv_uniq = u }) = text "KiCoBindsVar" <> angleBrackets (ppr u)
