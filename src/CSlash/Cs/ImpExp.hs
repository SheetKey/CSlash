{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module CSlash.Cs.ImpExp
  ( module CSlash.Language.Syntax.ImpExp
  , module CSlash.Cs.ImpExp
  ) where

import CSlash.Language.Syntax.Extension
import CSlash.Language.Syntax.Module.Name
import CSlash.Language.Syntax.ImpExp

import CSlash.Types.SourceText   ( SourceText(..) )
import CSlash.Types.SrcLoc
import CSlash.Types.Name
import CSlash.Types.PkgQual

import CSlash.Parser.Annotation
import CSlash.Cs.Extension

import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Data.Data
import Data.Maybe
-- import GHC.Hs.Doc (LHsDoc)

type instance Anno (ImportDecl (CsPass p)) = SrcSpanAnnA

importDeclQualifiedStyle :: Maybe EpaLocation -> (Maybe EpaLocation, ImportDeclQualifiedStyle)
importDeclQualifiedStyle mPost =
  if isJust mPost then (mPost, QualifiedPost) else (Nothing, NotQualified)

isImportDeclQualified :: ImportDeclQualifiedStyle -> Bool
isImportDeclQualified NotQualified = False
isImportDeclQualified _ = True

type instance ImportDeclPkgQual Ps = RawPkgQual
type instance ImportDeclPkgQual Rn = PkgQual
type instance ImportDeclPkgQual Tc = PkgQual

type instance XCImportDecl Ps = XImportDeclPass
type instance XCImportDecl Rn = XImportDeclPass
type instance XCImportDecl Tc = DataConCantHappen

data XImportDeclPass = XImportDeclPass
  { ideclAnn :: EpAnn EpAnnImportDecl
  , ideclSourceText :: SourceText
  , ideclImplicit :: Bool
  }
  deriving (Data)

type instance Anno ModuleName = SrcSpanAnnA
type instance Anno [LocatedA (IE (CsPass p))] = SrcSpanAnnL

deriving instance Data (IEWrappedName Ps)
deriving instance Data (IEWrappedName Rn)
deriving instance Data (IEWrappedName Tc)

deriving instance Eq (IEWrappedName Ps)
deriving instance Eq (IEWrappedName Rn)
deriving instance Eq (IEWrappedName Tc)

data EpAnnImportDecl = EpAnnImportDecl
  { importDeclAnnImport :: EpaLocation
  , importDeclAnnQualified :: Maybe EpaLocation
  , importDeclAnnPackage :: Maybe EpaLocation
  , importDeclAnnAs :: Maybe EpaLocation
  }
  deriving (Data)

instance NoAnn EpAnnImportDecl where
  noAnn = EpAnnImportDecl noAnn Nothing Nothing Nothing 

simpleImportDecl :: ModuleName -> ImportDecl Ps
simpleImportDecl mn = ImportDecl
  { ideclExt = XImportDeclPass noAnn NoSourceText False
  , ideclName = noLocA mn
  , ideclPkgQual = NoRawPkgQual
  , ideclQualified = NotQualified
  , ideclAs = Nothing
  , ideclImportList = Nothing
  }

instance ( OutputableBndrId p
         , Outputable (Anno (IE (CsPass p))))
  => Outputable (ImportDecl (CsPass p)) where
  ppr impdecl = ppr_impdecl impdecl


ppr_impdecl
  :: forall p.
     (OutputableBndrId p, Outputable (Anno (IE (CsPass p))))
  => ImportDecl (CsPass p) -> SDoc
ppr_impdecl (ImportDecl { ideclExt = impExt
                        , ideclName = mod'
                        , ideclAs = as
                        , ideclImportList = spec })
  = hang (hsep [ text "import"
               , ppr_implicit impExt
               , ppr mod'
               , pp_qualas as ])
         4 (pp_spec spec)
  where
    ppr_implicit ext =
      let implicit = case csPass @p of
                       Ps | XImportDeclPass {ideclImplicit = implicit} <- ext -> implicit
                       Rn | XImportDeclPass {ideclImplicit = implicit} <- ext -> implicit
                       Tc -> dataConCantHappen ext
      in if implicit
         then text "(implicit)"
         else empty
    pp_qualas Nothing = empty
    pp_qualas (Just a) = text "qualified as" <+> ppr a
    pp_spec Nothing = empty
    pp_spec (Just (Exactly, (L _ ies))) = ppr_ies ies
    pp_spec (Just (EverythingBut, (L _ ies))) = text "hiding" <+> ppr_ies ies
    ppr_ies [] = text "()"
    ppr_ies ies = char '(' <+> interpp'SP ies <+> char ')'

type instance XIEName (CsPass _) = NoExtField
type instance XIETyName (CsPass _) = EpaLocation

type instance Anno (IEWrappedName (CsPass _)) = SrcSpanAnnA

type instance Anno (IE (CsPass p)) = SrcSpanAnnA

type instance XIEVar Ps = NoExtField
type instance XIEVar Rn = NoExtField
type instance XIEVar Tc = NoExtField

type instance XIEModuleContents Ps = [AddEpAnn]
type instance XIEModuleContents Rn = NoExtField
type instance XIEModuleContents Tc = NoExtField

type instance XIETyVar Ps = NoExtField
type instance XIETyVar Rn = NoExtField
type instance XIETyVar Tc = NoExtField

type instance Anno (LocatedA (IE (CsPass p))) = SrcSpanAnnA

ieName :: IE (CsPass p) -> IdP (CsPass p)
ieName (IEVar _ (L _ n)) = ieWrappedName n
ieName _ = panic "ieName failed pattern match!"

ieWrappedLName :: IEWrappedName (CsPass p) -> LIdP (CsPass p)
ieWrappedLName (IEName _ n) = n
ieWrappedLName (IETyName _ n) = n

ieWrappedName :: IEWrappedName (CsPass p) -> IdP (CsPass p)
ieWrappedName = unLoc . ieWrappedLName

replaceWrappedName :: IEWrappedName Ps -> IdP Rn -> IEWrappedName Rn
replaceWrappedName (IEName x (L l _)) n = IEName x (L l n)
replaceWrappedName (IETyName r (L l _)) n = IETyName r (L l n)

instance OutputableBndrId p => Outputable (IE (CsPass p)) where
  ppr (IEVar _ var) = ppr (unLoc var)
  ppr (IEModuleContents _ mod') = text "module" <+> ppr mod'

instance OutputableBndrId p => Outputable (IEWrappedName (CsPass p)) where
  ppr (IEName _ (L _ n)) = pprPrefixOcc n
  ppr (IETyName _ (L _ n)) = text "type" <+> pprPrefixOcc n
