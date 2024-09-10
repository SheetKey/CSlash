{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Types.Avail where

import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set

import CSlash.Utils.Binary
-- import CSlash.Data.List.SetOps
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Constants (debugIsOn)

import Control.DeepSeq
import Data.Data ( Data )
import Data.Functor.Classes ( liftCompare )
import Data.List ( find )
import qualified Data.Semigroup as S

data AvailInfo
  = Avail Name
  | AvailTC Name [Name]
  deriving Data

type Avails = [AvailInfo]
