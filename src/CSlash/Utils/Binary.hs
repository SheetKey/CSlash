module CSlash.Utils.Binary
  ( module X
  , module CSlash.Utils.Binary
  ) where

import {-# SOURCE #-} CSlash.Types.Name (Name)
import CSlash.Types.SrcLoc
import qualified CSlash.Data.Strict as Strict

import Data.Coerce

import GHC.Utils.Binary as X hiding
  ( BinLocated (..), BinSpan (..), BinSrcSpan (..)
  , BindingName (..), simpleBindingNameWriter, simpleBindingNameReader
  )

newtype BindingName = BindingName { getBindingName :: Name }
  deriving (Eq)

simpleBindingNameWriter :: BinaryWriter Name -> BinaryWriter BindingName
simpleBindingNameWriter = coerce

simpleBindingNameReader :: BinaryReader Name -> BinaryReader BindingName
simpleBindingNameReader = coerce

newtype BinLocated a = BinLocated { unBinLocated :: Located a }

instance Binary a => Binary (BinLocated a) where
  put_ bh (BinLocated (L l x)) = do
    put_ bh $ BinSrcSpan l
    put_ bh x

  get bh = do
    l <- unBinSrcSpan <$> get bh
    x <- get bh
    return $ BinLocated $ L l x

newtype BinSpan = BinSpan { unBinSpan :: RealSrcSpan }

instance Binary BinSpan where
  put_ bh (BinSpan ss) = do
            put_ bh (srcSpanFile ss)
            put_ bh (srcSpanStartLine ss)
            put_ bh (srcSpanStartCol ss)
            put_ bh (srcSpanEndLine ss)
            put_ bh (srcSpanEndCol ss)

  get bh = do
            f <- get bh
            sl <- get bh
            sc <- get bh
            el <- get bh
            ec <- get bh
            return $ BinSpan (mkRealSrcSpan (mkRealSrcLoc f sl sc)
                                            (mkRealSrcLoc f el ec))
instance Binary UnhelpfulSpanReason where
  put_ bh r = case r of
    UnhelpfulNoLocationInfo -> putByte bh 0
    UnhelpfulWiredIn        -> putByte bh 1
    UnhelpfulInteractive    -> putByte bh 2
    UnhelpfulGenerated      -> putByte bh 3
    UnhelpfulOther fs       -> putByte bh 4 >> put_ bh fs

  get bh = do
    h <- getByte bh
    case h of
      0 -> return UnhelpfulNoLocationInfo
      1 -> return UnhelpfulWiredIn
      2 -> return UnhelpfulInteractive
      3 -> return UnhelpfulGenerated
      _ -> UnhelpfulOther <$> get bh

newtype BinSrcSpan = BinSrcSpan { unBinSrcSpan :: SrcSpan }

instance Binary BinSrcSpan where
  put_ bh (BinSrcSpan (RealSrcSpan ss _sb)) = do
          putByte bh 0
          put_ bh $ BinSpan ss

  put_ bh (BinSrcSpan (UnhelpfulSpan s)) = do
          putByte bh 1
          put_ bh s

  get bh = do
          h <- getByte bh
          case h of
            0 -> do BinSpan ss <- get bh
                    return $ BinSrcSpan (RealSrcSpan ss Strict.Nothing)
            _ -> do s <- get bh
                    return $ BinSrcSpan (UnhelpfulSpan s)
