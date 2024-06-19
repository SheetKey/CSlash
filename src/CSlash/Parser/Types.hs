module CSlash.Parser.Types
  ( PatBuilder(..) )
  where

data PatBuilder p
  = PatBuilderPat (Pat p)
  | PatBuilderPar (EpToken "(") (LocatedA (PatBuilder p)) (EpToken ")")
  | PatBuilderApp (LocatedA (PatBuilder p)) (LocatedA (PatBuilder p))
  | PatBuilderAppType (LocatedA (PatBuilder p)) (CsTyPar Ps)
  | PatBuilderOpApp (LocatedA (PatBuilder p)) (LocatedN RdrName)
                    (LocatedA (PatBuilder p)) [AddEpAnn]
  | PatBuilderVar (LocatedN RdrName)
  | PatBuilderOverLit (CsOverLit Ps)
