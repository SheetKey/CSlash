module CSlash.Tc.Types.BasicTypes where

import Prelude hiding ((<>))

import CSlash.Types.Id
import CSlash.Types.Basic
import CSlash.Types.Var
import CSlash.Types.SrcLoc
import CSlash.Types.Name
import CSlash.Types.TyThing
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set
import CSlash.Tc.Types.Origin
import CSlash.Tc.Utils.TcType

import CSlash.Cs.Extension ( Rn )

import CSlash.Language.Syntax.Type ( LCsSigType )

-- import GHC.Tc.Errors.Types.PromotionErr (PromotionErr, peCategory)

import CSlash.Core.TyCon  ( TyCon, tyConKind )
import CSlash.Utils.Outputable
import CSlash.Utils.Misc

type TcBinderStack = [TcBinder]

type TcId = Id

data TcBinder
  = TcIdBndr TcId TopLevelFlag
  | TcIdBndr_ExpType Name ExpType TopLevelFlag
  | TcTvBndr Name TypeVar

instance Outputable TcBinder where
  ppr (TcIdBndr id top_lvl) = ppr id <> brackets (ppr top_lvl)
  ppr (TcIdBndr_ExpType id _ top_lvl) = ppr id <> brackets (ppr top_lvl)
  ppr (TcTvBndr name tv) = ppr name <+> ppr tv

instance HasOccName TcBinder where
  occName (TcIdBndr id _) = occName (idName id)
  occName (TcIdBndr_ExpType name _ _) = occName name
  occName (TcTvBndr name _) = occName name

{- *********************************************************************
*                                                                      *
             TcTyThing
*                                                                      *
********************************************************************* -}

data TcTyThing
  = AGlobal TyThing
  | ATcId
    { tct_id :: Id
    , tct_info :: IdBindingInfo
    }
  | ATyVar Name TcTyVar
  | ATcTyCon TyCon

data IdBindingInfo
  = NotLetBound
  | ClosedLet
  | NonClosedLet RhsNames ClosedTypeId

type RhsNames = NameSet

type ClosedTypeId = Bool
