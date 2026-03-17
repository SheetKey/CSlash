module CSlash.Core.Map.Expr where

import CSlash.Data.TrieMap
-- import CSlash.Core.Map.Type
import CSlash.Core
import CSlash.Core.Type
import CSlash.Types.Tickish
import CSlash.Types.Var

import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Outputable

import qualified Data.Map    as Map
import CSlash.Types.Name.Env
import Control.Monad( (>=>) )
import CSlash.Types.Literal (Literal)

-- {-# SPECIALIZE lkG :: Key CoreMapX     -> CoreMapG a     -> Maybe a #-}
-- {-# SPECIALIZE xtG :: Key CoreMapX     -> XT a -> CoreMapG a -> CoreMapG a #-}
-- {-# SPECIALIZE mapG :: (a -> b) -> CoreMapG a     -> CoreMapG b #-}
-- {-# SPECIALIZE fdG :: (a -> b -> b) -> CoreMapG a     -> b -> b #-}

{- *********************************************************************
*                                                                      *
                   CoreMap
*                                                                      *
********************************************************************* -}

newtype CoreMap a = CoreMap (CoreMapG a)

type CoreMapG = GenMap CoreMapX

data CoreMapX a = CM

instance Outputable a => Outputable (CoreMap a)

emptyCoreMap :: CoreMap a
emptyCoreMap = panic "emptyTM"
