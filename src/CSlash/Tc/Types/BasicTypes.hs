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

import CSlash.Core.TyCon  ( TyCon, AnyTyCon, tyConKind )
import CSlash.Utils.Outputable
import CSlash.Utils.Misc

---------------------------
-- The TcBinderStack
---------------------------

type TcBinderStack = [TcBinder]

type TcId = Id (AnyTyVar AnyKiVar) AnyKiVar

data TcBinder
  = TcIdBndr TcId TopLevelFlag
  | TcIdBndr_ExpType Name ExpType TopLevelFlag
  | TcTvBndr Name (TcTyVar AnyKiVar)
  | TcKvBndr Name AnyKiVar

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
             Type signatures
*                                                                      *
********************************************************************* -}

type TcSigFun = Name -> Maybe TcSigInfo

data TcSigInfo = TcIdSig TcCompleteSig

data TcCompleteSig = CSig
  { sig_bndr :: TcId
  , sig_ctxt :: UserTypeCtxt
  , sig_loc :: SrcSpan
  }

tcSigInfoName :: TcSigInfo -> Name
tcSigInfoName (TcIdSig sig) = idName (sig_bndr sig)

completeSigPolyId :: TcSigInfo -> TcId
completeSigPolyId (TcIdSig sig) = sig_bndr sig

instance Outputable TcCompleteSig where
  ppr (CSig { sig_bndr = bndr }) = ppr bndr <+> colon <+> ppr (varType bndr)

{- *********************************************************************
*                                                                      *
             TcTyKiThing
*                                                                      *
********************************************************************* -}

data TcTyKiThing
  = AGlobal (TyThing (AnyTyVar AnyKiVar) AnyKiVar)
  | ATcId
    { tct_id :: TcId
    , tct_info :: IdBindingInfo
    }
  | ATyVar Name (TcTyVar AnyKiVar)
  | AKiVar Name AnyKiVar -- should make a new type 'TcKiThing'
  | ATcTyCon AnyTyCon

tcTyThingTyCon_maybe :: TcTyKiThing -> Maybe AnyTyCon
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
                      <+> colon <+> ppr (varKind tv)
  ppr (AKiVar n kv) = text "Kind variable" <+> quotes (ppr n) <+> equals <+> ppr kv
  ppr (ATcTyCon tc) = text "ATcTyCon" <+> ppr tc <+> colon <+> ppr (tyConKind tc)

data IdBindingInfo
  = NotLetBound
  | ClosedLet
  | NonClosedLet RhsNames ClosedTypeId

data IsGroupClosed
  = IsGroupClosed (NameEnv RhsNames) ClosedTypeId

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
