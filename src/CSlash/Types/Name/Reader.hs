module CSlash.Types.Name.Reader where

import CSlash.Language.Syntax.Module.Name

import CSlash.Types.SrcLoc
import CSlash.Types.Unique
import CSlash.Types.Name
import CSlash.Types.Name.Occurrence
import CSlash.Unit.Types

data RdrName
  = Unqual OccName
  | Qual ModuleName OccName
  | Orig Module OccName
  | Exact Name

nukeExact :: Name -> RdrName
nukeExact n
  | isExternalName n = Orig (nameModule n) (nameOccName n)
  | otherwise = Unqual (nameOccName n)

instance Eq RdrName where
  (Exact n1) == (Exact n2) = n1 == n2
  (Exact n1) == r2@(Orig _ _) = nukeExact n1 == r2
  r1@(Orig _ _) == (Exact n2) = r1 == nukeExact n2
  (Orig m1 o1) == (Orig m2 o2) = m1 == m2 && o1 == o2
  (Qual m1 o1) == (Qual m2 o2) = m1 == m2 && o1 == o2
  (Unqual o1) == (Unqual o2) = o1 == o2
  _ == _ = False
