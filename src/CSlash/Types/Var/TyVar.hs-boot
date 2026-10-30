{-# LANGUAGE RoleAnnotations #-}

module CSlash.Types.Var.TyVar where

type role TyVar nominal
data TyVar p

type role PiTyBinder nominal
data PiTyBinder p