{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE KindSignatures #-}

module CSlash.Types.Var.CoVar where

type role CoVar nominal nominal
data CoVar (thing :: * -> *) p
