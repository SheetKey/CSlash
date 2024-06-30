{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module CSlash.Cs.Doc
  ( WithCsDocIdentifiers(..)
  ) where

import CSlash.Utils.Binary
import CSlash.Utils.Outputable
import CSlash.Types.SrcLoc
import CSlash.Language.Syntax.Extension
import CSlash.Cs.Extension

import Control.DeepSeq
import Data.Data

data WithCsDocIdentifiers a pass = WithCsDocIdentifiers
  { csDocString :: !a
  , csDocIdentifiers :: ![Located (IdP pass)]
  }

deriving instance (Data pass, Data (IdP pass), Data a) => Data (WithCsDocIdentifiers a pass)
deriving instance (Eq (IdP pass), Eq a) => Eq (WithCsDocIdentifiers a pass)
instance (NFData (IdP pass), NFData a) => NFData (WithCsDocIdentifiers a pass) where
  rnf (WithCsDocIdentifiers d i) = rnf d `seq` rnf i

instance Outputable a => Outputable (WithCsDocIdentifiers a pass) where
  ppr (WithCsDocIdentifiers s _ids) = ppr s

instance Binary a => Binary (WithCsDocIdentifiers a Rn) where
  put_ bh (WithCsDocIdentifiers s ids) = do
    put_ bh s
    put_ bh $ BinLocated <$> ids
  get bh =
    liftA2 WithCsDocIdentifiers (get bh) (fmap unBinLocated <$> get bh)
