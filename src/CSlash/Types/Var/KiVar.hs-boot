{-# LANGUAGE RoleAnnotations #-}

module CSlash.Types.Var.KiVar where

import {-# SOURCE #-} CSlash.Types.Var.Class (IsVar)

type role KiVar nominal
data KiVar p

instance IsVar (KiVar p)