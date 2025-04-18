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
  | TcKvBndr Name KindVar

instance Outputable TcBinder where
  ppr (TcIdBndr id top_lvl) = ppr id <> brackets (ppr top_lvl)
  ppr (TcIdBndr_ExpType id _ top_lvl) = ppr id <> brackets (ppr top_lvl)
  ppr (TcTvBndr name tv) = ppr name <+> ppr tv
  ppr (TcKvBndr name kv) = ppr name <+> ppr kv

instance HasOccName TcBinder where
  occName (TcIdBndr id _) = occName (idName id)
  occName (TcIdBndr_ExpType name _ _) = occName name
  occName (TcTvBndr name _) = occName name
  occName (TcKvBndr name _) = occName name

{- *********************************************************************
*                                                                      *
             TcTyKiThing
*                                                                      *
********************************************************************* -}

data TcTyKiThing
  = AGlobal TyThing
  | ATcId
    { tct_id :: Id
    , tct_info :: IdBindingInfo
    }
  | ATyVar Name TcTyVar
  | AKiVar Name TcKiVar -- should make a new type 'TcKiThing'
  | ATcTyCon TyCon

tcTyThingTyCon_maybe :: TcTyKiThing -> Maybe TyCon
tcTyThingTyCon_maybe (AGlobal (ATyCon tc)) = Just tc
tcTyThingTyCon_maybe (ATcTyCon tc_tc) = Just tc_tc
tcTyThingTyCon_maybe _ = Nothing

instance Outputable TcTyKiThing where
  ppr (AGlobal g) = ppr g
  ppr elt@(ATcId {}) = text "Identifier"
                        <> brackets (ppr (tct_id elt) <> colon
                                     <> ppr (varType (tct_id elt))
                                     <> comma
                                     <+> ppr (tct_info elt))
  ppr (ATyVar n tv) = text "Type variable" <+> quotes (ppr n) <+> equals <+> ppr tv
                      <+> colon <+> ppr (varType tv)
  ppr (AKiVar n kv) = text "Kind variable" <+> quotes (ppr n) <+> equals <+> ppr kv
  ppr (ATcTyCon tc) = text "ATcTyCon" <+> ppr tc <+> colon <+> ppr (tyConKind tc)

data IdBindingInfo
  = NotLetBound
  | ClosedLet
  | NonClosedLet RhsNames ClosedTypeId

type RhsNames = NameSet

type ClosedTypeId = Bool

instance Outputable IdBindingInfo where
  ppr NotLetBound = text "NotLetBound"
  ppr ClosedLet = text "TopLevelLet"
  ppr (NonClosedLet fvs closed_type) = text "TopLevelLet" <+> ppr fvs <+> ppr closed_type

pprTcTyKiThingCategory :: TcTyKiThing -> SDoc
pprTcTyKiThingCategory = text . capitalise . tcTyKiThingCategory

tcTyKiThingCategory :: TcTyKiThing -> String
tcTyKiThingCategory (AGlobal thing) = tyThingCategory thing
tcTyKiThingCategory (ATyVar {}) = "type variable"
tcTyKiThingCategory (AKiVar {}) = "kind variable"
tcTyKiThingCategory (ATcId {}) = "local identifier"
tcTyKiThingCategory (ATcTyCon {}) = "local tycon"
