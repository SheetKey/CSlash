module CSlash.Core.Map.Type where

import CSlash.Cs.Pass

import CSlash.Core.Type
import CSlash.Core.Type.Rep
import CSlash.Core.TyCon( isForgetfulSynTyCon )
import CSlash.Data.TrieMap

import CSlash.Data.FastString
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Unique.FM
import CSlash.Utils.Outputable

import CSlash.Utils.Panic

import qualified Data.Map    as Map
import qualified Data.IntMap as IntMap

import Control.Monad ( (>=>) )

-- {-# SPECIALIZE lkG :: Key TypeMapX     -> TypeMapG a     -> Maybe a #-}
-- {-# SPECIALIZE lkG :: Key CoercionMapX -> CoercionMapG a -> Maybe a #-}
-- 
-- {-# SPECIALIZE xtG :: Key TypeMapX     -> XT a -> TypeMapG a -> TypeMapG a #-}
-- {-# SPECIALIZE xtG :: Key CoercionMapX -> XT a -> CoercionMapG a -> CoercionMapG a #-}
-- 
-- {-# SPECIALIZE mapG :: (a -> b) -> TypeMapG a     -> TypeMapG b #-}
-- {-# SPECIALIZE mapG :: (a -> b) -> CoercionMapG a -> CoercionMapG b #-}
-- 
-- {-# SPECIALIZE fdG :: (a -> b -> b) -> TypeMapG a     -> b -> b #-}
-- {-# SPECIALIZE fdG :: (a -> b -> b) -> CoercionMapG a -> b -> b #-}

{- *********************************************************************
*                                                                      *
                   Coercions
*                                                                      *
********************************************************************* -}

{- *********************************************************************
*                                                                      *
                   Types
*                                                                      *
********************************************************************** -}

{- *********************************************************************
*                                                                      *
                   Variables
*                                                                      *
********************************************************************* -}

type BoundVar = Int

data CmEnv = CME
  { cme_next :: !BoundVar
  , cme_env :: VarEnv (Id Zk) BoundVar }

emptyCME :: CmEnv
emptyCME = CME { cme_next = 0, cme_env = emptyVarEnv }

data DeBruijn a = D CmEnv a

deBruijnize :: a -> DeBruijn a
deBruijnize = D emptyCME

instance 
