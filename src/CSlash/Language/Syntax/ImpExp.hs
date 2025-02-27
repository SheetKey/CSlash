{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Language.Syntax.ImpExp where

import CSlash.Language.Syntax.Extension
import CSlash.Language.Syntax.Module.Name

import Data.Data

-- | Located Import Declaration
type LImportDecl pass = XRec pass (ImportDecl pass)

data ImportListInterpretation = Exactly | EverythingBut
  deriving (Eq, Data)

data ImportDeclQualifiedStyle
  = QualifiedPost
  | NotQualified
  deriving (Eq, Data)

-- | Import Declaration
data ImportDecl pass = ImportDecl
  { ideclExt :: XCImportDecl pass
  , ideclName :: XRec pass ModuleName
  , ideclPkgQual :: ImportDeclPkgQual pass
  , ideclQualified :: ImportDeclQualifiedStyle
  , ideclAs :: Maybe (XRec pass ModuleName)
  , ideclImportList :: Maybe (ImportListInterpretation, XRec pass [LIE pass])
  }

-- | Located Import or Export
type LIE pass = XRec pass (IE pass)

-- | Imported or exported entity
data IE pass
  = IEVar (XIEVar pass) (LIEWrappedName pass)
  | IEModuleContents (XIEModuleContents pass) (XRec pass ModuleName)

data IEWrappedName p
  = IEName (XIEName p) (LIdP p)
  | IETyName (XIETyName p) (LIdP p) -- GHC IEType
    
type LIEWrappedName p = XRec p (IEWrappedName p)
