{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}

module CSlash.Types.Var.Class where

import CSlash.Types.Name (Name)

class IsVar v where
varName :: IsVar v => v -> Name

class VarHasKind tv p | tv -> p
