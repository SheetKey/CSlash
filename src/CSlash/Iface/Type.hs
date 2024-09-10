module CSlash.Iface.Type where

import {-# SOURCE #-} CSlash.Builtin.Types
  ( tupleTyConName
  , tupleDataConName
  , sumTyCon )
-- import GHC.Core.Type ( isRuntimeRepTy, isMultiplicityTy, isLevityTy, funTyFlagTyCon )
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

{- **********************************************************************
*                                                                       *
                IfaceType
*                                                                       *
********************************************************************** -}

data IfaceType
  = IfaceFreeTyVar TypeVar
  | IfaceTyVar IfLclName
  | IfaceAppTy IfaceType IfaceAppArgs
  | IfaceFunTy IfaceKind IfaceType IfaceType
  | IfaceForAllTy IfaceForAllBndr IfaceType
  | IfaceTyConApp IfaceTyCon IfaceAppArgs
  | IfaceTupleTy IfaceAppArgs
  | IfaceWithContext IfaceKind IfaceType

type IfaceForAllBndr = VarBndr IfaceBndr ForAllTyFlag

data IfaceAppArgs
  = IA_Nil
  | IA_Arg IfaceType ForAllTyFlag IfaceAppArgs

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

data IfaceTyConInfo = IfaceTyConInfo { ifaceTyConSort :: IfaceTyConSort }
  deriving (Eq)
