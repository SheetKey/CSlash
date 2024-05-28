module CSlash.Types.Name where

import CSlash.Types.Name.Occurrence
import CSlash.Types.Unique
import CSlash.Types.SrcLoc

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
