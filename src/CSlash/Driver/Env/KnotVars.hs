{-# LANGUAGE DeriveFunctor #-}

module CSlash.Driver.Env.KnotVars where

import CSlash.Unit.Types ( Module )
import CSlash.Unit.Module.Env
import Data.Maybe
import CSlash.Utils.Outputable

data KnotVars a
  = KnotVars
    { kv_domain :: [Module]
    , kv_lookup :: Module -> Maybe a
    }
  | NoKnotVars
  deriving Functor

instance Outputable (KnotVars a) where
  ppr NoKnotVars = text "NoKnot"
  ppr (KnotVars dom _) = text "Knotty:" <+> ppr dom
