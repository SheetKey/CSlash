{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module CSlash.Types.Tickish
  ( GenTickish(..)
  , CsTickish
  ) where

import CSlash.Unit.Module

import Data.Data

data TickishPass
  = TickishPassCs

type CsTickish = GenTickish 'TickishPassCs

data GenTickish pass
  = CpcTick -- CSlash program coverage tick
    { tickModule :: Module
    , tickId :: !Int
    }

deriving instance Eq (GenTickish 'TickishPassCs)
deriving instance Ord (GenTickish 'TickishPassCs)
deriving instance Data (GenTickish 'TickishPassCs)
