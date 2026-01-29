{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE KindSignatures #-}

module CSlash.Types.Var.CoVar where

type role CoVar representational nominal
data CoVar (thing :: * -> *) p
