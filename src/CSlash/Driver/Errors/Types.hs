module CSlash.Driver.Errors.Types where

import Data.Bifunctor
import Data.Typeable

import CSlash.Driver.DynFlags (DynFlags, PackageArg, gopt)
import CSlash.Driver.Flags (GeneralFlag (Opt_BuildingCabalPackage))
import CSlash.Types.Error
import CSlash.Unit.Module
-- import GHC.Unit.State

import CSlash.Parser.Errors.Types ( PsMessage(PsHeaderMessage) )
-- import GHC.HsToCore.Errors.Types ( DsMessage )
import CSlash.Cs.Extension          (Tc)

-- import Language.Haskell.Syntax.Decls (RuleDecl)
-- import qualified GHC.LanguageExtensions as LangExt

-- import GHC.Generics ( Generic )

-- import GHC.Tc.Errors.Types
-- import GHC.Iface.Errors.Types

data CsMessage where
  CsPsMessage :: PsMessage -> CsMessage
