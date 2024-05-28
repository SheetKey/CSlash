module CSlash.Types.Name.Reader where

import CSlash.Language.Syntax.Module.Name

import CSlash.Types.SrcLoc
import CSlash.Types.Unique
import CSlash.Types.Name
import CSlash.Types.Name.Occurrence
import CSlash.Unit.Module

data RdrName
  = Unqual OccName
  | Qual ModuleName OccName
  | Orig Module OccName
  | Exact Name
