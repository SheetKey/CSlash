module CSlash.Core where

import CSlash.Types.Var
import CSlash.Core.Type
import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.Tickish
import CSlash.Core.DataCon
import CSlash.Unit.Module
import CSlash.Types.Basic
import CSlash.Types.Unique.Set

import CSlash.Utils.Binary
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Data.Data hiding (TyCon)
import Data.Int
import Data.Word

{- *********************************************************************
*                                                                      *
            The main data types
*                                                                      *
********************************************************************* -}

data AltCon
  = DataAlt DataCon
  | LitAlt Literal
  | DEFAULT
  deriving (Eq, Data)

{- *********************************************************************
*                                                                      *
                Unfoldings
*                                                                      *
********************************************************************* -}

data Unfolding
  = NoUnfolding
  | OtherCon [AltCon]
  
