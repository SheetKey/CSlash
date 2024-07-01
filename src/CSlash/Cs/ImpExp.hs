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

import CSlash.Parser.Annotation
import CSlash.Hs.Extension

import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Data.Data
import Data.Maybe
import GHC.Hs.Doc (LHsDoc)

type instance Anno (ImportDecl (CsPass p)) = SrcSpanAnnA

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
type instance Anno [LocatedA (IO (CsPass p))] = SrcSpanAnnL

instance ( OutputableBndrId p
         , Outputable (Anno (IE (CsPass p))))
  => Outputable (ImportDecl (CsPass p)) where
  ppr (ImportDecl { ideclExt = impExt
                  , ideclName = mod'
                  , ideclAs = as
                  , ideclImportList = spec })
    = hang (hsep [ text "import"
                 , ppr_implicit impExt
                 , ppr pkg
                 , ppr mod'
                 , pp_qualas as ])
           4 (pp_spec spec)
    where
      pp_implicit ext =
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
