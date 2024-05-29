module CSlash.Language.Syntax (
  ModuleName(..), CsModule(..)
  ) where

import CSlash.Language.Syntax.Extension
import CSlash.Language.Syntax.Module.Name
import CSlash.Language.Syntax.ImpExp
import CSlash.Language.Syntax.Decls

-- | Top-level structure of a module.
data CsModule p = CsModule
  { csmodName :: Maybe (XRec p ModuleName)
  , hsmodExports :: Maybe (XRec p [LIE p])
  , hsmodImports :: [LImportDecl p]
  , hsmodDecls :: [LCsDecl p]
  }
