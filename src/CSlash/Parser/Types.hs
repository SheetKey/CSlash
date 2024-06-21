{-# LANGUAGE DataKinds #-}

module CSlash.Parser.Types
  ( PatBuilder(..) )
  where

import CSlash.Cs.Extension

import CSlash.Parser.Annotation

import CSlash.Types.Name.Reader

import CSlash.Language.Syntax.Type
import CSlash.Language.Syntax.Pat
import CSlash.Language.Syntax.Lit

data PatBuilder p
  = PatBuilderPat (Pat p)
  | PatBuilderPar (EpToken "(") (LocatedA (PatBuilder p)) (EpToken ")")
  | PatBuilderApp (LocatedA (PatBuilder p)) (LocatedA (PatBuilder p))
  | PatBuilderAppType (LocatedA (PatBuilder p)) (CsTyPat Ps)
  | PatBuilderOpApp (LocatedA (PatBuilder p)) (LocatedN RdrName)
                    (LocatedA (PatBuilder p)) [AddEpAnn]
  | PatBuilderVar (LocatedN RdrName)
  | PatBuilderOverLit (CsOverLit Ps)
