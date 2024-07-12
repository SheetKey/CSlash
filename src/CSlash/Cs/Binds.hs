{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module CSlash.Cs.Binds
  ( module CSlash.Language.Syntax.Binds
  , module CSlash.Cs.Binds
  ) where

import Prelude hiding ((<>))

import CSlash.Language.Syntax.Binds

import {-# SOURCE #-} CSlash.Cs.Expr (pprExpr, pprFunBind)

import CSlash.Language.Syntax.Extension
import CSlash.Cs.Extension
import CSlash.Cs.Type
import CSlash.Cs.Kind
import CSlash.Types.Tickish
import CSlash.Types.SrcLoc
import CSlash.Types.Name.Set
import CSlash.Parser.Annotation
import CSlash.Utils.Outputable

import Data.Data

type instance XFunBind (CsPass pL) Ps = AddEpAnn
type instance XFunBind (CsPass pL) Rn = NameSet
type instance XFunBind (CsPass pL) Tc = [CsTickish]

type instance XTyFunBind (CsPass pL) Ps = [AddEpAnn]
type instance XTyFunBind (CsPass pL) Rn = NameSet
type instance XTyFunBind (CsPass pL) Tc = [CsTickish]

type instance XTCVarBind (CsPass pL) (CsPass pR) = XTCVarBindCs pL pR
type family XTCVarBindCs pL pR where
  XTCVarBindCs 'Typechecked 'Typechecked = NoExtField
  XTCVarBindCs _ _ = DataConCantHappen

instance (OutputableBndrId pl, OutputableBndrId pr)
  => Outputable (CsBindLR (CsPass pl) (CsPass pr)) where
  ppr mbind = ppr_monobind mbind

ppr_monobind :: forall idL idR.
                (OutputableBndrId idL, OutputableBndrId idR)
             => CsBindLR (CsPass idL) (CsPass idR) -> SDoc
ppr_monobind (FunBind { fun_id = fun
                      , fun_body = body
                      , fun_ext = ticks })
  = pprTicks empty ticksDoc
    $$ whenPprDebug (pprBndr LetBind (unLoc fun))
    $$ ppr body
    $$ whenPprDebug (pprIfTc @idR $ wrapDoc)
  where
    ticksDoc :: SDoc
    ticksDoc = case csPass @idR of
                 Ps -> empty
                 Rn -> empty
                 Tc -> if null ticks
                       then empty
                       else text "-- ticks = " <> ppr ticks
    wrapDoc :: SDoc
    wrapDoc = empty
ppr_monobind (TyFunBind _ _ _) = text "TyFunBind ppr non implemented"
ppr_monobind (TCVarBind { tcvar_id = var, tcvar_rhs = rhs })
  = sep [pprBndr CasePatBind var, nest 2 $ equals <+> pprExpr (unLoc rhs)]

pprTicks :: SDoc -> SDoc -> SDoc
pprTicks pp_no_debug pp_when_debug
  = getPprStyle $ \ sty ->
    getPprDebug $ \ debug ->
                    if debug || dumpStyle sty
                    then pp_when_debug
                    else pp_no_debug

type instance XTypeSig (CsPass p) = AnnSig
type instance XKindSig (CsPass p) = AnnSig
type instance XFixSig (CsPass p) = [AddEpAnn]

type instance XFixitySig Ps = NamespaceSpecifier
type instance XFixitySig Rn = NamespaceSpecifier
type instance XFixitySig Tc = NoExtField

data NamespaceSpecifier
  = NoNamespaceSpecifier
  | TypeNamespaceSpecifier (EpToken "type")
  deriving (Eq, Data)

data AnnSig = AnnSig
  { asColon :: AddEpAnn
  , asRest :: [AddEpAnn]
  }
  deriving Data

instance NoAnn AnnSig where
  noAnn = AnnSig noAnn noAnn

instance OutputableBndrId p => Outputable (Sig (CsPass p)) where
  ppr sig = ppr_sig sig

ppr_sig
  :: OutputableBndrId p
  => Sig (CsPass p) -> SDoc
ppr_sig (TypeSig _ var ty) = pprVarSig (unLoc var) (ppr ty)
ppr_sig (KindSig _ var kind) = pprVarSig (unLoc var) (ppr kind)
ppr_sig (FixSig _ fix_sig) = ppr fix_sig

instance OutputableBndrId p => Outputable (FixitySig (CsPass p)) where
  ppr (FixitySig _ name fixity) = sep [ppr fixity, pprop]
    where
      pprop = pprInfixOcc (unLoc name)

pprVarSig :: (OutputableBndr id) => id -> SDoc -> SDoc
pprVarSig var pp_ty = sep [ pprPrefixOcc var <+> colon, nest 2 pp_ty ]
