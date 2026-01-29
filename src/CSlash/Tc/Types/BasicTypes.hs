module CSlash.Tc.Types.BasicTypes where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Types.Var.Id
import CSlash.Types.Basic
import CSlash.Types.Var
import CSlash.Types.SrcLoc
import CSlash.Types.Name hiding (varName)
import CSlash.Types.TyThing
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set
import CSlash.Tc.Types.Origin
import CSlash.Tc.Utils.TcType

import CSlash.Language.Syntax.Type ( LCsSigType )

-- import GHC.Tc.Errors.Types.PromotionErr (PromotionErr, peCategory)

import CSlash.Core.TyCon  ( TyCon, pprTyConKind )
import CSlash.Utils.Outputable
import CSlash.Utils.Misc

---------------------------
-- The TcBinderStack
---------------------------

type TcBinderStack = [TcBinder]

data TcBinder
  = TcIdBndr (Id Tc) TopLevelFlag
  | TcIdBndr_ExpType Name ExpType TopLevelFlag
  | TcTvBndr Name TcTyVar
  | TcKvBndr Name TcKiVar

instance Outputable TcBinder where
  ppr (TcIdBndr id top_lvl) = ppr id <> brackets (ppr top_lvl)
  ppr (TcIdBndr_ExpType id _ top_lvl) = ppr id <> brackets (ppr top_lvl)
  ppr (TcTvBndr name tv) = ppr name <+> ppr tv
  ppr (TcKvBndr name kv) = ppr name <+> ppr kv

instance HasOccName TcBinder where
  occName (TcIdBndr id _) = occName (varName id)
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
  { sig_bndr :: Id Tc
  , sig_ctxt :: UserTypeCtxt
  , sig_loc :: SrcSpan
  }

hasCompleteSig :: TcSigFun -> Name -> Bool
hasCompleteSig sig_fn name
  = case sig_fn name of
      Just _ -> True
      _ -> False

tcSigInfoName :: TcSigInfo -> Name
tcSigInfoName (TcIdSig sig) = varName (sig_bndr sig)

completeSigPolyId :: TcSigInfo -> Id Tc
completeSigPolyId (TcIdSig sig) = sig_bndr sig

instance Outputable TcCompleteSig where
  ppr (CSig { sig_bndr = bndr }) = ppr bndr <+> colon <+> ppr (varType bndr)

{- *********************************************************************
*                                                                      *
             TcTyKiThing
*                                                                      *
********************************************************************* -}

data TcTyKiThing
  = AGlobal (TyThing Tc)
  | ATcId
    { tct_id :: Id Tc
    , tct_info :: IdBindingInfo
    }
  | ATyVar Name (TyVar Tc)
  | AKiVar Name (KiVar Tc) -- should make a new type 'TcKiThing'
  | ATcTyCon (TyCon Tc)

tcTyThingTyCon_maybe :: TcTyKiThing -> Maybe (TyCon Tc)
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
  ppr (ATcTyCon tc) = text "ATcTyCon" <+> ppr tc <+> colon <+> pprTyConKind tc

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
