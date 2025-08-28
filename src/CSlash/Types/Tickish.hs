{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module CSlash.Types.Tickish
  ( GenTickish(..)
  , CoreTickish
  ) where

import CSlash.Unit.Module

import CSlash.Utils.Outputable

import Data.Data

data TickishPass
  = TickishPassCs

type CoreTickish = GenTickish 'TickishPassCs

data GenTickish (pass :: TickishPass)
  = CpcTick -- CSlash program coverage tick
    { tickModule :: Module
    , tickId :: !Int
    }

deriving instance Eq (GenTickish 'TickishPassCs)
deriving instance Ord (GenTickish 'TickishPassCs)
deriving instance Data (GenTickish 'TickishPassCs)

-- FOUND IN GHC Core.Ppr
instance Outputable (GenTickish pass) where
  ppr (CpcTick modl ix) =
    hcat [ text "cpc<"
         , ppr modl, comma
         , ppr ix
         , text ">" ]
