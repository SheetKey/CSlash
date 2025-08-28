{-# LANGUAGE LambdaCase #-}
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

import {-# SOURCE #-} CSlash.Cs.Expr (pprExpr, pprLExpr, pprFunBind)

import CSlash.Language.Syntax.Extension
import CSlash.Cs.Extension
import CSlash.Cs.Type
import CSlash.Cs.Kind
import CSlash.Types.Tickish
import CSlash.Tc.Types.Evidence
import CSlash.Types.SourceText
import CSlash.Types.SrcLoc as SrcLoc
import CSlash.Types.Var
import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.Basic
import CSlash.Data.Bag
import CSlash.Parser.Annotation
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc ((<||>))

import Data.Function
import Data.List (sortBy)
import Data.Data

type instance XCsValBinds (CsPass pL) (CsPass pR) = EpAnn AnnList
type instance XEmptyLocalBinds (CsPass pL) (CsPass pR) = NoExtField

data NCsValBindsLR idL
  = NValBinds [(RecFlag, LCsBinds idL)] [LSig Rn]

type instance XValBinds (CsPass pL) (CsPass pR) = AnnSortKey BindTag
type instance XXValBindsLR (CsPass pL) pR = NCsValBindsLR (CsPass pL)

type instance XFunBind (CsPass pL) Ps = AddEpAnn
type instance XFunBind (CsPass pL) Rn = NameSet
type instance XFunBind (CsPass pL) Tc = (CsWrapper, [CoreTickish])

type instance XTyFunBind (CsPass pL) Ps = [AddEpAnn]
type instance XTyFunBind (CsPass pL) Rn = ([Name], FreeVars)
type instance XTyFunBind (CsPass pL) Tc = NoExtField

type instance XXCsBindsLR Ps pR = DataConCantHappen
type instance XXCsBindsLR Rn pR = DataConCantHappen
type instance XXCsBindsLR Tc pR = AbsBinds

type instance XTCVarBind (CsPass pL) (CsPass pR) = XTCVarBindCs pL pR
type family XTCVarBindCs pL pR where
  XTCVarBindCs 'Typechecked 'Typechecked = NoExtField
  XTCVarBindCs _ _ = DataConCantHappen

-- ---------------------------------------------------------------------

data AbsBinds = AbsBinds
  { abs_tvs :: [TyVar KiVar]
  , abs_exports :: [ABExport]
  , abs_binds :: LCsBinds Tc
  , abs_sig :: Bool
  }

data ABExport = ABE
  { abe_poly :: Id (TyVar KiVar) KiVar
  , abe_mono :: Id (TyVar KiVar) KiVar
  }

-- ---------------------------------------------------------------------

instance (OutputableBndrId pl, OutputableBndrId pr)
         => Outputable (CsValBindsLR (CsPass pl) (CsPass pr)) where
  ppr (ValBinds _ binds sigs)
    = pprDeclList (pprLCsBindsForUser binds sigs)
  ppr (XValBindsLR (NValBinds sccs sigs))
    = getPprDebug $ \case
        True -> vcat (map ppr sigs) $$ vcat (map ppr_scc sccs)
        False -> pprDeclList (pprLCsBindsForUser (concat (map snd sccs)) sigs)
    where
      ppr_scc (ref_flag, binds) = pp_rec ref_flag <+> pprLCsBinds binds
      pp_rec Recursive = text "rec"
      pp_rec NonRecursive = text "nonrec"

pprLCsBinds
  :: (OutputableBndrId idL, OutputableBndrId idR) => LCsBindsLR (CsPass idL) (CsPass idR) -> SDoc
pprLCsBinds binds
  | isEmptyLCsBinds binds = empty
  | otherwise = pprDeclList (map ppr binds)

pprLCsBindsForUser
  :: (OutputableBndrId idL, OutputableBndrId idR, OutputableBndrId id2)
  => LCsBindsLR (CsPass idL) (CsPass idR) -> [LSig (CsPass id2)] -> [SDoc]
pprLCsBindsForUser binds sigs = map snd (sort_by_loc decls)
  where
    decls :: [(SrcSpan, SDoc)]
    decls = [(locA loc, ppr sig) | L loc sig <- sigs] ++
            [(locA loc, ppr bind) | L loc bind <- binds]

    sort_by_loc decls = sortBy (SrcLoc.leftmost_smallest `on` fst) decls

pprDeclList :: [SDoc] -> SDoc
pprDeclList ds = pprDeeperList vcat ds

isEmptyValBinds :: CsValBindsLR (CsPass a) (CsPass b) -> Bool
isEmptyValBinds (ValBinds _ ds sigs) = isEmptyLCsBinds ds && null sigs
isEmptyValBinds (XValBindsLR (NValBinds ds sigs)) = null ds && null sigs

emptyValBindsIn :: CsValBindsLR (CsPass a) (CsPass b)
emptyValBindsIn = ValBinds NoAnnSortKey [] []

emptyValBindsOut :: CsValBindsLR (CsPass a) (CsPass b)
emptyValBindsOut = XValBindsLR (NValBinds [] [])

emptyLCsBinds :: LCsBindsLR (CsPass idL) idR
emptyLCsBinds = []

isEmptyLCsBinds :: LCsBindsLR (CsPass idL) idR -> Bool
isEmptyLCsBinds = null

plusCsValBinds :: CsValBinds (CsPass a) -> CsValBinds (CsPass a) -> CsValBinds (CsPass a) 
plusCsValBinds (ValBinds _ ds1 sigs1) (ValBinds _ ds2 sigs2)
  = ValBinds NoAnnSortKey (ds1 ++ ds2) (sigs1 ++ sigs2)
plusCsValBinds (XValBindsLR (NValBinds ds1 sigs1)) (XValBindsLR (NValBinds ds2 sigs2))
  = XValBindsLR (NValBinds (ds1 ++ ds2) (sigs1 ++ sigs2))
plusCsValBinds _ _ = panic "plusCsValBinds"

instance (OutputableBndrId pl, OutputableBndrId pr)
         => Outputable (CsBindLR (CsPass pl) (CsPass pr)) where
  ppr mbind = ppr_monobind mbind

ppr_monobind :: forall idL idR.
                (OutputableBndrId idL, OutputableBndrId idR)
             => CsBindLR (CsPass idL) (CsPass idR) -> SDoc
ppr_monobind (FunBind { fun_id = fun
                      , fun_body = body
                      , fun_ext = ext })
  = pprTicks empty ticksDoc
    $$ whenPprDebug (pprBndr LetBind (unLoc fun))
    $$ pprLExpr body
    $$ whenPprDebug (pprIfTc @idR $ wrapDoc)
  where
    ticksDoc :: SDoc
    ticksDoc = case csPass @idR of
                 Ps -> empty
                 Rn -> empty
                 Tc | (_, ticks) <- ext ->
                      if null ticks
                      then empty
                      else text "-- ticks = " <> ppr ticks
    wrapDoc :: SDoc
    wrapDoc = case csPass @idR of
                Ps -> empty
                Rn -> empty
                Tc | (wrap, _) <- ext -> ppr wrap

ppr_monobind (TyFunBind _ _ _) = text "TyFunBind ppr non implemented"
ppr_monobind (TCVarBind { tcvar_id = var, tcvar_rhs = rhs })
  = sep [pprBndr CasePatBind var, nest 2 $ equals <+> pprExpr (unLoc rhs)]
ppr_monobind (XCsBindsLR b) = case csPass @idL of
  Tc -> ppr_absbinds b
    where
      ppr_absbinds (AbsBinds { abs_tvs = tyvars, abs_exports = exports, abs_binds = val_binds })
        = sdocOption sdocPrintTypecheckerElaboration $ \case
            False -> pprLCsBinds val_binds
            True -> hang (text "AbsBinds" <+> brackets (interpp'SP tyvars))
                    2 $ braces $ vcat
                    [ text "Exports:" <+> brackets (sep (punctuate comma (map ppr exports)))
                    , text "Exported types:"
                      <+> vcat [pprBndr LetBind (abe_poly ex) | ex <- exports]
                    , text "Binds:" <+> pprLCsBinds val_binds
                    ]

instance Outputable ABExport where
  ppr (ABE { abe_poly = gbl, abe_mono = lcl })
    = sep [ppr gbl, nest 2 (text "<=" <+> ppr lcl)]


pprTicks :: SDoc -> SDoc -> SDoc
pprTicks pp_no_debug pp_when_debug
  = getPprStyle $ \ sty ->
    getPprDebug $ \ debug ->
                    if debug || dumpStyle sty
                    then pp_when_debug
                    else pp_no_debug

type instance XTypeSig (CsPass p) = AnnSig
type instance XKindSig (CsPass p) = AnnSig
type instance XFixSig (CsPass p) = ([AddEpAnn], SourceText)

type instance XFixitySig Ps = NamespaceSpecifier
type instance XFixitySig Rn = NamespaceSpecifier
type instance XFixitySig Tc = NoExtField

data NamespaceSpecifier
  = NoNamespaceSpecifier
  | TypeNamespaceSpecifier (EpToken "type")
  deriving (Eq, Data)

coveredByNamespaceSpecifier :: NamespaceSpecifier -> NameSpace -> Bool
coveredByNamespaceSpecifier NoNamespaceSpecifier = const True
coveredByNamespaceSpecifier TypeNamespaceSpecifier{} = isTcClsNameSpace <||> isTvNameSpace

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

csSigDoc :: Sig (CsPass p) -> SDoc
csSigDoc (TypeSig {}) = text "type signature"
csSigDoc (FixSig {}) = text "fixity declaration"
csSigDoc (KindSig {}) = text "kind signature"

instance OutputableBndrId p => Outputable (FixitySig (CsPass p)) where
  ppr (FixitySig _ name fixity) = sep [ppr fixity, pprop]
    where
      pprop = pprInfixOcc (unLoc name)

pprVarSig :: (OutputableBndr id) => id -> SDoc -> SDoc
pprVarSig var pp_ty = sep [ pprPrefixOcc var <+> colon, nest 2 pp_ty ]

{- *********************************************************************
*                                                                      *
            Anno instances
*                                                                      *
********************************************************************* -}

type instance Anno (CsBindLR (CsPass idL) (CsPass idR)) = SrcSpanAnnA
type instance Anno (Sig (CsPass p)) = SrcSpanAnnA

type instance Anno (FixitySig (CsPass p)) = SrcSpanAnnA
