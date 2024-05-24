module CSlash.Language.Syntax (
  ModuleName(..), CsModule(..)
  ) where

import CSlash.Language.Extension
import CSlash.Language.Module.Name

-- | Top-level structure of a module.
data CsModule p = CsModule
  { csmodName :: Maybe (XRec p ModuleName)
  , hsmodExports :: Maybe (XRec p [LIE p])
  , hsmodImports :: [LImportDecl p]
  , hsmodDecls :: [LDecl p]
  }
