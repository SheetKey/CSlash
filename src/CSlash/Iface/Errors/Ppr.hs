{-# LANGUAGE LambdaCase #-}

module CSlash.Iface.Errors.Ppr where

import Prelude hiding ((<>))

import CSlash.Types.Error
import CSlash.Types.Hint.Ppr () 
import CSlash.Types.Error.Codes
import CSlash.Types.Name
import CSlash.Types.TyThing

import CSlash.Unit.State
import CSlash.Unit.Module

import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import CSlash.Iface.Errors.Types

readInterfaceErrorDiagnostic :: ReadInterfaceError -> SDoc
readInterfaceErrorDiagnostic = \case
  ExceptionOccurred fp ex ->
    hang (text "Exception when reading interface file " <+> text fp)
    2 (text (show ex))
  HiModuleNameMismatchWarn _ m1 m2 -> hiModuleNameMismatchWarn m1 m2

hiModuleNameMismatchWarn :: Module -> Module -> SDoc
hiModuleNameMismatchWarn requested_mod read_mod
  | moduleUnit requested_mod == moduleUnit read_mod
  = sep [ text "Interface file contains module" <+> quotes (ppr read_mod) <> comma
        , text "but we were expecting module" <+> quotes (ppr requested_mod)
        , sep [ text "Probable cause: the source code which generated interface file"
              , text "has an incompatible module name"
              ]
        ]
  | otherwise
  = withPprStyle (mkUserStyle alwaysQualify AllTheWay) $
    hsep [ text "Something is amiss; requested module "
         , ppr requested_mod
         , text "differs from the name found in the interface file"
         , ppr read_mod
         , parens (text "if these names look the same, try again with -dppr-debug")
         ]
