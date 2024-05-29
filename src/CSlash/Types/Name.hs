module CSlash.Types.Name where

import CSlash.Types.Name.Occurrence
import CSlash.Types.Unique
import CSlash.Types.SrcLoc
import CSlash.Types.TyThing
import CSlash.Unit.Types

data Name = Name
  { n_sort :: NameSort
  , n_occ :: OccName
  , n_uniq :: {-# UNPACK #-} !Unique
  , n_loc :: !SrcSpan
  }

data NameSort
  = External Module
  | WiredIn Module TyThing BuiltInSyntax
  | Internal
  | System

data BuiltInSyntax = BuiltInSyntax | UserSyntax
