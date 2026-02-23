{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module CSlash.Types.Tickish where

import CSlash.Unit.Module

import CSlash.Utils.Outputable
import CSlash.Utils.Panic

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

tickishCounts :: GenTickish pass -> Bool
tickishCounts CpcTick{} = True

data TickishScoping
  = NoScope
  | SoftScope
  deriving Eq

tickishScoped :: GenTickish pass -> TickishScoping
tickishScoped CpcTick{} = NoScope

tickishScopesLike :: GenTickish pass -> TickishScoping -> Bool
tickishScopesLike t scope = tickishScoped t `like` scope
  where like NoScope _ = True
        like _ NoScope = False
        like SoftScope _ = True
        like _ SoftScope = False

tickishFloatable :: GenTickish pass -> Bool
tickishFloatable t = t `tickishScopesLike` SoftScope && not (tickishCounts t)

tickishCanSplit :: GenTickish pass -> Bool
tickishCanSplit CpcTick{} = False

mkNoCount :: GenTickish pass -> GenTickish pass
mkNoCount n | not (tickishCounts n) = n
            | not (tickishCanSplit n) = panic "mkNoCount: Cannot split!"
mkNoCount CpcTick{} = panic "mkNoCount: Undefined split!"

mkNoScope :: GenTickish pass -> GenTickish pass
mkNoScope n | tickishScoped n == NoScope = n
            | not (tickishCanSplit n) = panic "mkNoScope: Cannot split!"
mkNoScope CpcTick{} = panic "mkNoScope: Undefined split!"

tickishIsCode :: GenTickish pass -> Bool
tickishIsCode CpcTick{} = True

data TickishPlacement
  = PlaceRuntime
  deriving (Eq, Show)

instance Outputable TickishPlacement where
  ppr = text . show

tickishPlace :: GenTickish pass -> TickishPlacement
tickishPlace CpcTick{} = PlaceRuntime

tickishContains :: Eq (GenTickish pass) => GenTickish pass -> GenTickish pass -> Bool
tickishContains t1@CpcTick{} t2@CpcTick{} = t1 == t2
