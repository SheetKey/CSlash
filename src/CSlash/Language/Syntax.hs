module CSlash.Language.Syntax
  ( module CSlash.Language.Syntax.Binds
  , module CSlash.Language.Syntax.Decls
  , module CSlash.Language.Syntax.Expr
  , module CSlash.Language.Syntax.ImpExp
  , module CSlash.Language.Syntax.Lit
  , module CSlash.Language.Syntax.Module.Name
  , module CSlash.Language.Syntax.Pat
  , module CSlash.Language.Syntax.Type
  , module CSlash.Language.Syntax.Extension
  , ModuleName(..), CsModule(..)
  ) where

import CSlash.Language.Syntax.Binds
import CSlash.Language.Syntax.Decls
import CSlash.Language.Syntax.Expr
import CSlash.Language.Syntax.ImpExp
import CSlash.Language.Syntax.Lit
import CSlash.Language.Syntax.Module.Name
import CSlash.Language.Syntax.Pat
import CSlash.Language.Syntax.Type
import CSlash.Language.Syntax.Extension

-- | Top-level structure of a module.
data CsModule p = CsModule
  { csmodName :: Maybe (XRec p ModuleName)
  , hsmodExports :: Maybe (XRec p [LIE p])
  , hsmodImports :: [LImportDecl p]
  , hsmodDecls :: [LCsDecl p]
  }
