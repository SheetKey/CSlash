-- {-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UnboxedTuples #-}

{-# OPTIONS_GHC -O2 -funbox-strict-fields #-}

module CSlash.Utils.Binary
  ( Bin,
    Binary(..),
    BinHandle,
    SymbolTable, Dictionary,

    BinData(..), dataHandle, handleData,
    unsafeUnpackBinBuffer,
    
    openBinMem,

    seekBin,
    tellBin,
    castBin,
    withBinBuffer,

    foldGet, foldGet',
    
    writeBinMem,
    readBinMem,
    readBinMemN,

    putAt, getAt,
    forwardPut, forwardPut_, forwardGet,

    putByte,
    getByte,
    putByteString,
    getByteString,
    
    putULEB128,
    getULEB128,
    putSLEB128,
    getSLEB128,

    FixedLengthEncoding(..),

    lazyGet,
    lazyPut,
    lazyGetMaybe,
    lazyPutMaybe,

    UserData(..), getUserData, setUserData,
    newReadState, newWriteState, noUserData,

    putDictionary, getDictionary, putFS,
    FSTable, initFSTable, getDictFastString, putDictFastString,

    BinSpan(..), BinSrcSpan(..), BinLocated(..)
  ) where

import CSlash.Language.Syntax.Module.Name (ModuleName(..))

import {-# SOURCE #-} CSlash.Types.Name (Name)
import CSlash.Data.FastString
import CSlash.Utils.Panic.Plain
import CSlash.Types.Unique.FM
import CSlash.Data.FastMutInt
import CSlash.Utils.Fingerprint
import CSlash.Types.SrcLoc
import CSlash.Types.Unique
import qualified CSlash.Data.Strict as Strict
import CSlash.Utils.Outputable( JoinPointHood(..) )

import Control.DeepSeq
import Foreign hiding (shiftL, shiftR, void)
import Data.Array
import Data.Array.IO
import Data.Array.Unsafe
import Data.Bits
import Data.ByteString (ByteString)
import qualified Data.ByteString.Internal as BS
import qualified Data.ByteString.Unsafe   as BS
import Data.IORef
import Data.Char                ( ord, chr )
import Data.List.NonEmpty       ( NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Set                 ( Set )
import qualified Data.Set as Set
import Data.Time
import Data.List (unfoldr)
import Control.Monad            ( when, (<$!>), unless, forM_, void )
import System.IO as IO
import System.IO.Unsafe         ( unsafeInterleaveIO )
import System.IO.Error          ( mkIOError, eofErrorType )
import GHC.Real                 ( Ratio(..) )
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import GHC.ForeignPtr           ( unsafeWithForeignPtr )

type BinArray = ForeignPtr Word8

data BinData = BinData Int BinArray

instance NFData BinData where
  rnf (BinData sz _) = rnf sz

instance Binary BinData where
  put_ bh (BinData sz dat) = do
    put_ bh sz
    putPrim bh sz $ \dest ->
      unsafeWithForeignPtr dat $ \orig ->
        copyBytes dest orig sz
  --
  get bh = do
    sz <- get bh
    dat <- mallocForeignPtrBytes sz
    getPrim bh sz $ \orig ->
      unsafeWithForeignPtr dat $ \dest ->
        copyBytes dest orig sz
    return (BinData sz dat)

dataHandle :: BinData -> IO BinHandle
dataHandle (BinData size bin) = do
  ixr <- newFastMutInt 0
  szr <- newFastMutInt size
  binr <- newIORef bin
  return (BinMem noUserData ixr szr binr)

handleData :: BinHandle -> IO BinData
handleData (BinMem _ ixr _ binr) = BinData <$> readFastMutInt ixr <*> readIORef binr

data BinHandle
  = BinMem {  
     bh_usr :: UserData,
     _off_r :: !FastMutInt,
     _sz_r  :: !FastMutInt,
     _arr_r :: !(IORef BinArray)
    }

getUserData :: BinHandle -> UserData
getUserData bh = bh_usr bh

setUserData :: BinHandle -> UserData -> BinHandle
setUserData bh us = bh { bh_usr = us }

withBinBuffer :: BinHandle -> (ByteString -> IO a) -> IO a
withBinBuffer (BinMem _ ix_r _ arr_r) action = do
  arr <- readIORef arr_r
  ix <- readFastMutInt ix_r
  action $ BS.fromForeignPtr arr 0 ix

unsafeUnpackBinBuffer :: ByteString -> IO BinHandle
unsafeUnpackBinBuffer (BS.BS arr len) = do
  arr_r <- newIORef arr
  ix_r <- newFastMutInt 0
  sz_r <- newFastMutInt len
  return (BinMem noUserData ix_r sz_r arr_r)

newtype Bin a = BinPtr Int
  deriving (Eq, Ord, Show, Bounded)

castBin :: Bin a -> Bin b
castBin (BinPtr i) = BinPtr i

class Binary a where
    put_   :: BinHandle -> a -> IO ()
    put    :: BinHandle -> a -> IO (Bin a)
    get    :: BinHandle -> IO a

    put_ bh a = do _ <- put bh a; return ()
    put bh a  = do p <- tellBin bh; put_ bh a; return p

putAt  :: Binary a => BinHandle -> Bin a -> a -> IO ()
putAt bh p x = do seekBin bh p; put_ bh x; return ()

getAt  :: Binary a => BinHandle -> Bin a -> IO a
getAt bh p = do seekBin bh p; get bh

openBinMem :: Int -> IO BinHandle
openBinMem size
 | size <= 0 = error "GHC.Utils.Binary.openBinMem: size must be >= 0"
 | otherwise = do
   arr <- mallocForeignPtrBytes size
   arr_r <- newIORef arr
   ix_r <- newFastMutInt 0
   sz_r <- newFastMutInt size
   return (BinMem noUserData ix_r sz_r arr_r)

tellBin :: BinHandle -> IO (Bin a)
tellBin (BinMem _ r _ _) = do ix <- readFastMutInt r; return (BinPtr ix)

seekBin :: BinHandle -> Bin a -> IO ()
seekBin h@(BinMem _ ix_r sz_r _) (BinPtr !p) = do
  sz <- readFastMutInt sz_r
  if (p > sz)
        then do expandBin h p; writeFastMutInt ix_r p
        else writeFastMutInt ix_r p

seekBinNoExpand :: BinHandle -> Bin a -> IO ()
seekBinNoExpand (BinMem _ ix_r sz_r _) (BinPtr !p) = do
  sz <- readFastMutInt sz_r
  if (p > sz)
        then panic "seekBinNoExpand: seek out of range"
        else writeFastMutInt ix_r p

writeBinMem :: BinHandle -> FilePath -> IO ()
writeBinMem (BinMem _ ix_r _ arr_r) fn = do
  h <- openBinaryFile fn WriteMode
  arr <- readIORef arr_r
  ix  <- readFastMutInt ix_r
  unsafeWithForeignPtr arr $ \p -> hPutBuf h p ix
  hClose h

readBinMem :: FilePath -> IO BinHandle
readBinMem filename = do
  withBinaryFile filename ReadMode $ \h -> do
    filesize' <- hFileSize h
    let filesize = fromIntegral filesize'
    readBinMem_ filesize h

readBinMemN :: Int -> FilePath -> IO (Maybe BinHandle)
readBinMemN size filename = do
  withBinaryFile filename ReadMode $ \h -> do
    filesize' <- hFileSize h
    let filesize = fromIntegral filesize'
    if filesize < size
      then pure Nothing
      else Just <$> readBinMem_ size h

readBinMem_ :: Int -> Handle -> IO BinHandle
readBinMem_ filesize h = do
  arr <- mallocForeignPtrBytes filesize
  count <- unsafeWithForeignPtr arr $ \p -> hGetBuf h p filesize
  when (count /= filesize) $
       error ("Binary.readBinMem: only read " ++ show count ++ " bytes")
  arr_r <- newIORef arr
  ix_r <- newFastMutInt 0
  sz_r <- newFastMutInt filesize
  return (BinMem noUserData ix_r sz_r arr_r)

expandBin :: BinHandle -> Int -> IO ()
expandBin (BinMem _ _ sz_r arr_r) !off = do
   !sz <- readFastMutInt sz_r
   let !sz' = getSize sz
   arr <- readIORef arr_r
   arr' <- mallocForeignPtrBytes sz'
   withForeignPtr arr $ \old ->
     withForeignPtr arr' $ \new ->
       copyBytes new old sz
   writeFastMutInt sz_r sz'
   writeIORef arr_r arr'
   where
    getSize :: Int -> Int
    getSize !sz
      | sz > off
      = sz
      | otherwise
      = getSize (sz * 2)

foldGet
  :: Binary a
  => Word -- n elements
  -> BinHandle
  -> b -- initial accumulator
  -> (Word -> a -> b -> IO b)
  -> IO b
foldGet n bh init_b f = go 0 init_b
  where
    go i b
      | i == n    = return b
      | otherwise = do
          a <- get bh
          b' <- f i a b
          go (i+1) b'

foldGet'
  :: Binary a
  => Word -- n elements
  -> BinHandle
  -> b -- initial accumulator
  -> (Word -> a -> b -> IO b)
  -> IO b
{-# INLINE foldGet' #-}
foldGet' n bh init_b f = go 0 init_b
  where
    go i !b
      | i == n    = return b
      | otherwise = do
          !a  <- get bh
          b'  <- f i a b
          go (i+1) b'

putPrim :: BinHandle -> Int -> (Ptr Word8 -> IO ()) -> IO ()
putPrim h@(BinMem _ ix_r sz_r arr_r) size f = do
  ix <- readFastMutInt ix_r
  sz <- readFastMutInt sz_r
  when (ix + size > sz) $
    expandBin h (ix + size)
  arr <- readIORef arr_r
  unsafeWithForeignPtr arr $ \op -> f (op `plusPtr` ix)
  writeFastMutInt ix_r (ix + size)

getPrim :: BinHandle -> Int -> (Ptr Word8 -> IO a) -> IO a
getPrim (BinMem _ ix_r sz_r arr_r) size f = do
  ix <- readFastMutInt ix_r
  sz <- readFastMutInt sz_r
  when (ix + size > sz) $
      ioError (mkIOError eofErrorType "Data.Binary.getPrim" Nothing Nothing)
  arr <- readIORef arr_r
  w <- unsafeWithForeignPtr arr $ \p -> f (p `plusPtr` ix)
  writeFastMutInt ix_r (ix + size)
  return w

putWord8 :: BinHandle -> Word8 -> IO ()
putWord8 h !w = putPrim h 1 (\op -> poke op w)

getWord8 :: BinHandle -> IO Word8
getWord8 h = getPrim h 1 peek

putWord16 :: BinHandle -> Word16 -> IO ()
putWord16 h w = putPrim h 2 (\op -> do
  pokeElemOff op 0 (fromIntegral (w `shiftR` 8))
  pokeElemOff op 1 (fromIntegral (w .&. 0xFF))
  )

getWord16 :: BinHandle -> IO Word16
getWord16 h = getPrim h 2 (\op -> do
  w0 <- fromIntegral <$> peekElemOff op 0
  w1 <- fromIntegral <$> peekElemOff op 1
  return $! w0 `shiftL` 8 .|. w1
  )

putWord32 :: BinHandle -> Word32 -> IO ()
putWord32 h w = putPrim h 4 (\op -> do
  pokeElemOff op 0 (fromIntegral (w `shiftR` 24))
  pokeElemOff op 1 (fromIntegral ((w `shiftR` 16) .&. 0xFF))
  pokeElemOff op 2 (fromIntegral ((w `shiftR` 8) .&. 0xFF))
  pokeElemOff op 3 (fromIntegral (w .&. 0xFF))
  )

getWord32 :: BinHandle -> IO Word32
getWord32 h = getPrim h 4 (\op -> do
  w0 <- fromIntegral <$> peekElemOff op 0
  w1 <- fromIntegral <$> peekElemOff op 1
  w2 <- fromIntegral <$> peekElemOff op 2
  w3 <- fromIntegral <$> peekElemOff op 3

  return $! (w0 `shiftL` 24) .|.
            (w1 `shiftL` 16) .|.
            (w2 `shiftL` 8)  .|.
            w3
  )

putWord64 :: BinHandle -> Word64 -> IO ()
putWord64 h w = putPrim h 8 (\op -> do
  pokeElemOff op 0 (fromIntegral (w `shiftR` 56))
  pokeElemOff op 1 (fromIntegral ((w `shiftR` 48) .&. 0xFF))
  pokeElemOff op 2 (fromIntegral ((w `shiftR` 40) .&. 0xFF))
  pokeElemOff op 3 (fromIntegral ((w `shiftR` 32) .&. 0xFF))
  pokeElemOff op 4 (fromIntegral ((w `shiftR` 24) .&. 0xFF))
  pokeElemOff op 5 (fromIntegral ((w `shiftR` 16) .&. 0xFF))
  pokeElemOff op 6 (fromIntegral ((w `shiftR` 8) .&. 0xFF))
  pokeElemOff op 7 (fromIntegral (w .&. 0xFF))
  )

getWord64 :: BinHandle -> IO Word64
getWord64 h = getPrim h 8 (\op -> do
  w0 <- fromIntegral <$> peekElemOff op 0
  w1 <- fromIntegral <$> peekElemOff op 1
  w2 <- fromIntegral <$> peekElemOff op 2
  w3 <- fromIntegral <$> peekElemOff op 3
  w4 <- fromIntegral <$> peekElemOff op 4
  w5 <- fromIntegral <$> peekElemOff op 5
  w6 <- fromIntegral <$> peekElemOff op 6
  w7 <- fromIntegral <$> peekElemOff op 7

  return $! (w0 `shiftL` 56) .|.
            (w1 `shiftL` 48) .|.
            (w2 `shiftL` 40) .|.
            (w3 `shiftL` 32) .|.
            (w4 `shiftL` 24) .|.
            (w5 `shiftL` 16) .|.
            (w6 `shiftL` 8)  .|.
            w7
  )

putByte :: BinHandle -> Word8 -> IO ()
putByte bh !w = putWord8 bh w

getByte :: BinHandle -> IO Word8
getByte h = getWord8 h

{-# SPECIALISE putULEB128 :: BinHandle -> Word -> IO () #-}
{-# SPECIALISE putULEB128 :: BinHandle -> Word64 -> IO () #-}
{-# SPECIALISE putULEB128 :: BinHandle -> Word32 -> IO () #-}
{-# SPECIALISE putULEB128 :: BinHandle -> Word16 -> IO () #-}
{-# SPECIALISE putULEB128 :: BinHandle -> Int -> IO () #-}
{-# SPECIALISE putULEB128 :: BinHandle -> Int64 -> IO () #-}
{-# SPECIALISE putULEB128 :: BinHandle -> Int32 -> IO () #-}
{-# SPECIALISE putULEB128 :: BinHandle -> Int16 -> IO () #-}
putULEB128 :: forall a. (Integral a, FiniteBits a) => BinHandle -> a -> IO ()
putULEB128 bh w =
-- #if defined(DEBUG)
--     (if w < 0 then panic "putULEB128: Signed number" else id) $
-- #endif
    go w
  where
    go :: a -> IO ()
    go w
      | w <= (127 :: a)
      = putByte bh (fromIntegral w :: Word8)
      | otherwise = do
        -- bit 7 (8th bit) indicates more to come.
        let !byte = setBit (fromIntegral w) 7 :: Word8
        putByte bh byte
        go (w `unsafeShiftR` 7)

{-# SPECIALISE getULEB128 :: BinHandle -> IO Word #-}
{-# SPECIALISE getULEB128 :: BinHandle -> IO Word64 #-}
{-# SPECIALISE getULEB128 :: BinHandle -> IO Word32 #-}
{-# SPECIALISE getULEB128 :: BinHandle -> IO Word16 #-}
{-# SPECIALISE getULEB128 :: BinHandle -> IO Int #-}
{-# SPECIALISE getULEB128 :: BinHandle -> IO Int64 #-}
{-# SPECIALISE getULEB128 :: BinHandle -> IO Int32 #-}
{-# SPECIALISE getULEB128 :: BinHandle -> IO Int16 #-}
getULEB128 :: forall a. (Integral a, FiniteBits a) => BinHandle -> IO a
getULEB128 bh =
    go 0 0
  where
    go :: Int -> a -> IO a
    go shift w = do
        b <- getByte bh
        let !hasMore = testBit b 7
        let !val = w .|. ((clearBit (fromIntegral b) 7) `unsafeShiftL` shift) :: a
        if hasMore
            then do
                go (shift+7) val
            else
                return $! val

-- Signed numbers
{-# SPECIALISE putSLEB128 :: BinHandle -> Word -> IO () #-}
{-# SPECIALISE putSLEB128 :: BinHandle -> Word64 -> IO () #-}
{-# SPECIALISE putSLEB128 :: BinHandle -> Word32 -> IO () #-}
{-# SPECIALISE putSLEB128 :: BinHandle -> Word16 -> IO () #-}
{-# SPECIALISE putSLEB128 :: BinHandle -> Int -> IO () #-}
{-# SPECIALISE putSLEB128 :: BinHandle -> Int64 -> IO () #-}
{-# SPECIALISE putSLEB128 :: BinHandle -> Int32 -> IO () #-}
{-# SPECIALISE putSLEB128 :: BinHandle -> Int16 -> IO () #-}
putSLEB128 :: forall a. (Integral a, Bits a) => BinHandle -> a -> IO ()
putSLEB128 bh initial = go initial
  where
    go :: a -> IO ()
    go val = do
        let !byte = fromIntegral (clearBit val 7) :: Word8
        let !val' = val `unsafeShiftR` 7
        let !signBit = testBit byte 6
        let !done =
                -- Unsigned value, val' == 0 and last value can
                -- be discriminated from a negative number.
                ((val' == 0 && not signBit) ||
                -- Signed value,
                 (val' == -1 && signBit))

        let !byte' = if done then byte else setBit byte 7
        putByte bh byte'

        unless done $ go val'

{-# SPECIALISE getSLEB128 :: BinHandle -> IO Word #-}
{-# SPECIALISE getSLEB128 :: BinHandle -> IO Word64 #-}
{-# SPECIALISE getSLEB128 :: BinHandle -> IO Word32 #-}
{-# SPECIALISE getSLEB128 :: BinHandle -> IO Word16 #-}
{-# SPECIALISE getSLEB128 :: BinHandle -> IO Int #-}
{-# SPECIALISE getSLEB128 :: BinHandle -> IO Int64 #-}
{-# SPECIALISE getSLEB128 :: BinHandle -> IO Int32 #-}
{-# SPECIALISE getSLEB128 :: BinHandle -> IO Int16 #-}
getSLEB128 :: forall a. (Show a, Integral a, FiniteBits a) => BinHandle -> IO a
getSLEB128 bh = do
    (val,shift,signed) <- go 0 0
    if signed && (shift < finiteBitSize val )
        then return $! ((complement 0 `unsafeShiftL` shift) .|. val)
        else return val
    where
        go :: Int -> a -> IO (a,Int,Bool)
        go shift val = do
            byte <- getByte bh
            let !byteVal = fromIntegral (clearBit byte 7) :: a
            let !val' = val .|. (byteVal `unsafeShiftL` shift)
            let !more = testBit byte 7
            let !shift' = shift+7
            if more
                then go (shift') val'
                else do
                    let !signed = testBit byte 6
                    return (val',shift',signed)

newtype FixedLengthEncoding a
  = FixedLengthEncoding { unFixedLength :: a }
  deriving (Eq,Ord,Show)

instance Binary (FixedLengthEncoding Word8) where
  put_ h (FixedLengthEncoding x) = putByte h x
  get h = FixedLengthEncoding <$> getByte h

instance Binary (FixedLengthEncoding Word16) where
  put_ h (FixedLengthEncoding x) = putWord16 h x
  get h = FixedLengthEncoding <$> getWord16 h

instance Binary (FixedLengthEncoding Word32) where
  put_ h (FixedLengthEncoding x) = putWord32 h x
  get h = FixedLengthEncoding <$> getWord32 h

instance Binary (FixedLengthEncoding Word64) where
  put_ h (FixedLengthEncoding x) = putWord64 h x
  get h = FixedLengthEncoding <$> getWord64 h

instance Binary Word8 where
  put_ bh !w = putWord8 bh w
  get  = getWord8

instance Binary Word16 where
  put_ = putULEB128
  get  = getULEB128

instance Binary Word32 where
  put_ = putULEB128
  get  = getULEB128

instance Binary Word64 where
  put_ = putULEB128
  get = getULEB128

instance Binary Int8 where
  put_ h w = put_ h (fromIntegral w :: Word8)
  get h    = do w <- get h; return $! (fromIntegral (w::Word8))

instance Binary Int16 where
  put_ = putSLEB128
  get = getSLEB128

instance Binary Int32 where
  put_ = putSLEB128
  get = getSLEB128

instance Binary Int64 where
  put_ h w = putSLEB128 h w
  get h    = getSLEB128 h

instance Binary () where
    put_ _ () = return ()
    get  _    = return ()

instance Binary Bool where
    put_ bh b = putByte bh (fromIntegral (fromEnum b))
    get  bh   = do x <- getWord8 bh; return $! (toEnum (fromIntegral x))

instance Binary Char where
    put_  bh c = put_ bh (fromIntegral (ord c) :: Word32)
    get  bh   = do x <- get bh; return $! (chr (fromIntegral (x :: Word32)))

instance Binary Int where
    put_ bh i = put_ bh (fromIntegral i :: Int64)
    get  bh = do
        x <- get bh
        return $! (fromIntegral (x :: Int64))

instance Binary a => Binary [a] where
    put_ bh l = do
        let len = length l
        put_ bh len
        mapM_ (put_ bh) l
    get bh = do
        len <- get bh :: IO Int -- Int is variable length encoded so only
                                -- one byte for small lists.
        let loop 0 = return []
            loop n = do a <- get bh; as <- loop (n-1); return (a:as)
        loop len

instance (Binary a, Ord a) => Binary (Set a) where
  put_ bh s = put_ bh (Set.toList s)
  get bh = Set.fromList <$> get bh

instance Binary a => Binary (NonEmpty a) where
    put_ bh = put_ bh . NonEmpty.toList
    get bh = NonEmpty.fromList <$> get bh

instance (Ix a, Binary a, Binary b) => Binary (Array a b) where
    put_ bh arr = do
        put_ bh $ bounds arr
        put_ bh $ elems arr
    get bh = do
        bounds <- get bh
        xs <- get bh
        return $ listArray bounds xs

instance (Binary a, Binary b) => Binary (a,b) where
    put_ bh (a,b) = do put_ bh a; put_ bh b
    get bh        = do a <- get bh
                       b <- get bh
                       return (a,b)

instance (Binary a, Binary b, Binary c) => Binary (a,b,c) where
    put_ bh (a,b,c) = do put_ bh a; put_ bh b; put_ bh c
    get bh          = do a <- get bh
                         b <- get bh
                         c <- get bh
                         return (a,b,c)

instance (Binary a, Binary b, Binary c, Binary d) => Binary (a,b,c,d) where
    put_ bh (a,b,c,d) = do put_ bh a; put_ bh b; put_ bh c; put_ bh d
    get bh            = do a <- get bh
                           b <- get bh
                           c <- get bh
                           d <- get bh
                           return (a,b,c,d)

instance (Binary a, Binary b, Binary c, Binary d, Binary e) => Binary (a,b,c,d, e) where
    put_ bh (a,b,c,d, e) = do put_ bh a; put_ bh b; put_ bh c; put_ bh d; put_ bh e;
    get bh               = do a <- get bh
                              b <- get bh
                              c <- get bh
                              d <- get bh
                              e <- get bh
                              return (a,b,c,d,e)

instance (Binary a, Binary b, Binary c, Binary d, Binary e, Binary f) => Binary (a,b,c,d, e, f) where
    put_ bh (a,b,c,d, e, f) = do put_ bh a; put_ bh b; put_ bh c; put_ bh d; put_ bh e; put_ bh f;
    get bh                  = do a <- get bh
                                 b <- get bh
                                 c <- get bh
                                 d <- get bh
                                 e <- get bh
                                 f <- get bh
                                 return (a,b,c,d,e,f)

instance (Binary a, Binary b, Binary c, Binary d, Binary e, Binary f, Binary g) => Binary (a,b,c,d,e,f,g) where
    put_ bh (a,b,c,d,e,f,g) = do put_ bh a; put_ bh b; put_ bh c; put_ bh d; put_ bh e; put_ bh f; put_ bh g
    get bh                  = do a <- get bh
                                 b <- get bh
                                 c <- get bh
                                 d <- get bh
                                 e <- get bh
                                 f <- get bh
                                 g <- get bh
                                 return (a,b,c,d,e,f,g)

instance Binary a => Binary (Maybe a) where
    put_ bh Nothing  = putByte bh 0
    put_ bh (Just a) = do putByte bh 1; put_ bh a
    get bh           = do h <- getWord8 bh
                          case h of
                            0 -> return Nothing
                            _ -> do x <- get bh; return (Just x)

instance Binary a => Binary (Strict.Maybe a) where
    put_ bh Strict.Nothing = putByte bh 0
    put_ bh (Strict.Just a) = do putByte bh 1; put_ bh a
    get bh =
      do h <- getWord8 bh
         case h of
           0 -> return Strict.Nothing
           _ -> do x <- get bh; return (Strict.Just x)

instance (Binary a, Binary b) => Binary (Either a b) where
    put_ bh (Left  a) = do putByte bh 0; put_ bh a
    put_ bh (Right b) = do putByte bh 1; put_ bh b
    get bh            = do h <- getWord8 bh
                           case h of
                             0 -> do a <- get bh ; return (Left a)
                             _ -> do b <- get bh ; return (Right b)

instance Binary UTCTime where
    put_ bh u = do put_ bh (utctDay u)
                   put_ bh (utctDayTime u)
    get bh = do day <- get bh
                dayTime <- get bh
                return $ UTCTime { utctDay = day, utctDayTime = dayTime }

instance Binary Day where
    put_ bh d = put_ bh (toModifiedJulianDay d)
    get bh = do i <- get bh
                return $ ModifiedJulianDay { toModifiedJulianDay = i }

instance Binary DiffTime where
    put_ bh dt = put_ bh (toRational dt)
    get bh = do r <- get bh
                return $ fromRational r

instance Binary JoinPointHood where
    put_ bh NotJoinPoint = putByte bh 0
    put_ bh (JoinPoint ar) = do
        putByte bh 1
        put_ bh ar
    get bh = do
        h <- getByte bh
        case h of
            0 -> return NotJoinPoint
            _ -> do { ar <- get bh; return (JoinPoint ar) }

instance Binary Integer where
    put_ bh i
      | i >= lo64 && i <= hi64 = do
          putWord8 bh 0
          put_ bh (fromIntegral i :: Int64)
      | otherwise = do
          if i < 0
            then putWord8 bh 1
            else putWord8 bh 2
          put_ bh (unroll $ abs i)
      where
        lo64 = fromIntegral (minBound :: Int64)
        hi64 = fromIntegral (maxBound :: Int64)
    get bh = do
      int_kind <- getWord8 bh
      case int_kind of
        0 -> fromIntegral <$!> (get bh :: IO Int64)
        -- Large integer
        1 -> negate <$!> getInt
        2 -> getInt
        _ -> panic "Binary Integer - Invalid byte"
        where
          getInt :: IO Integer
          getInt = roll <$!> (get bh :: IO [Word8])

unroll :: Integer -> [Word8]
unroll = unfoldr step
  where
    step 0 = Nothing
    step i = Just (fromIntegral i, i `shiftR` 8)

roll :: [Word8] -> Integer
roll   = foldl' unstep 0 . reverse
  where
    unstep a b = a `shiftL` 8 .|. fromIntegral b

instance (Binary a) => Binary (Ratio a) where
    put_ bh (a :% b) = do put_ bh a; put_ bh b
    get bh = do a <- get bh; b <- get bh; return (a :% b)

instance Binary (Bin a) where
  put_ bh (BinPtr i) = putWord32 bh (fromIntegral i :: Word32)
  get bh = do i <- getWord32 bh; return (BinPtr (fromIntegral (i :: Word32)))

forwardPut :: BinHandle -> (b -> IO a) -> IO b -> IO (a,b)
forwardPut bh put_A put_B = do
  -- write placeholder pointer to A
  pre_a <- tellBin bh
  put_ bh pre_a

  -- write B
  r_b <- put_B

  -- update A's pointer
  a <- tellBin bh
  putAt bh pre_a a
  seekBinNoExpand bh a

  -- write A
  r_a <- put_A r_b
  pure (r_a,r_b)

forwardPut_ :: BinHandle -> (b -> IO a) -> IO b -> IO ()
forwardPut_ bh put_A put_B = void $ forwardPut bh put_A put_B

-- | Read a value stored using a forward reference
forwardGet :: BinHandle -> IO a -> IO a
forwardGet bh get_A = do
    -- read forward reference
    p <- get bh -- a BinPtr
    -- store current position
    p_a <- tellBin bh
    -- go read the forward value, then seek back
    seekBinNoExpand bh p
    r <- get_A
    seekBinNoExpand bh p_a
    pure r

lazyPut :: Binary a => BinHandle -> a -> IO ()
lazyPut bh a = do
    -- output the obj with a ptr to skip over it:
    pre_a <- tellBin bh
    put_ bh pre_a       -- save a slot for the ptr
    put_ bh a           -- dump the object
    q <- tellBin bh     -- q = ptr to after object
    putAt bh pre_a q    -- fill in slot before a with ptr to q
    seekBin bh q        -- finally carry on writing at q

lazyGet :: Binary a => BinHandle -> IO a
lazyGet bh = do
    p <- get bh -- a BinPtr
    p_a <- tellBin bh
    a <- unsafeInterleaveIO $ do
        -- NB: Use a fresh off_r variable in the child thread, for thread
        -- safety.
        off_r <- newFastMutInt 0
        getAt bh { _off_r = off_r } p_a
    seekBin bh p -- skip over the object for now
    return a

lazyPutMaybe :: Binary a => BinHandle -> Maybe a -> IO ()
lazyPutMaybe bh Nothing  = putWord8 bh 0
lazyPutMaybe bh (Just x) = do
  putWord8 bh 1
  lazyPut bh x

-- | Deserialize a value serialized by 'lazyPutMaybe'.
lazyGetMaybe :: Binary a => BinHandle -> IO (Maybe a)
lazyGetMaybe bh = do
  h <- getWord8 bh
  case h of
    0 -> pure Nothing
    _ -> Just <$> lazyGet bh

data UserData =
   UserData {
        ud_get_name :: BinHandle -> IO Name,
        ud_get_fs   :: BinHandle -> IO FastString,
        ud_put_nonbinding_name :: BinHandle -> Name -> IO (),
        ud_put_binding_name :: BinHandle -> Name -> IO (),
        ud_put_fs   :: BinHandle -> FastString -> IO ()
   }

newReadState :: (BinHandle -> IO Name)
             -> (BinHandle -> IO FastString)
             -> UserData
newReadState get_name get_fs
  = UserData { ud_get_name = get_name,
               ud_get_fs   = get_fs,
               ud_put_nonbinding_name = undef "put_nonbinding_name",
               ud_put_binding_name    = undef "put_binding_name",
               ud_put_fs   = undef "put_fs"
             }

newWriteState :: (BinHandle -> Name -> IO ())
              -> (BinHandle -> Name -> IO ())
              -> (BinHandle -> FastString -> IO ())
              -> UserData
newWriteState put_nonbinding_name put_binding_name put_fs
  = UserData { ud_get_name = undef "get_name",
               ud_get_fs   = undef "get_fs",
               ud_put_nonbinding_name = put_nonbinding_name,
               ud_put_binding_name    = put_binding_name,
               ud_put_fs   = put_fs
             }

noUserData :: UserData
noUserData = UserData
  { ud_get_name            = undef "get_name"
  , ud_get_fs              = undef "get_fs"
  , ud_put_nonbinding_name = undef "put_nonbinding_name"
  , ud_put_binding_name    = undef "put_binding_name"
  , ud_put_fs              = undef "put_fs"
  }

undef :: String -> a
undef s = panic ("Binary.UserData: no " ++ s)

type Dictionary = Array Int FastString

putDictionary :: BinHandle -> Int -> UniqFM FastString (Int,FastString) -> IO ()
putDictionary bh sz dict = do
  put_ bh sz
  mapM_ (putFS bh) (elems (array (0,sz-1) (nonDetEltsUFM dict)))

getDictionary :: BinHandle -> IO Dictionary
getDictionary bh = do
  sz <- get bh :: IO Int
  mut_arr <- newArray_ (0, sz-1) :: IO (IOArray Int FastString)
  forM_ [0..(sz-1)] $ \i -> do
    fs <- getFS bh
    writeArray mut_arr i fs
  unsafeFreeze mut_arr

getDictFastString :: Dictionary -> BinHandle -> IO FastString
getDictFastString dict bh = do
    j <- get bh
    return $! (dict ! fromIntegral (j :: Word32))


initFSTable :: BinHandle -> IO (BinHandle, FSTable, IO Int)
initFSTable bh = do
  dict_next_ref <- newFastMutInt 0
  dict_map_ref <- newIORef emptyUFM
  let bin_dict = FSTable
        { fs_tab_next = dict_next_ref
        , fs_tab_map  = dict_map_ref
        }
  let put_dict = do
        fs_count <- readFastMutInt dict_next_ref
        dict_map  <- readIORef dict_map_ref
        putDictionary bh fs_count dict_map
        pure fs_count

  let ud = getUserData bh
  let ud_fs = ud { ud_put_fs = putDictFastString bin_dict }
  let bh_fs = setUserData bh ud_fs

  return (bh_fs,bin_dict,put_dict)

putDictFastString :: FSTable -> BinHandle -> FastString -> IO ()
putDictFastString dict bh fs = allocateFastString dict fs >>= put_ bh

allocateFastString :: FSTable -> FastString -> IO Word32
allocateFastString FSTable { fs_tab_next = j_r
                           , fs_tab_map  = out_r
                           } f = do
    out <- readIORef out_r
    let !uniq = getUnique f
    case lookupUFM_Directly out uniq of
        Just (j, _)  -> return (fromIntegral j :: Word32)
        Nothing -> do
           j <- readFastMutInt j_r
           writeFastMutInt j_r (j + 1)
           writeIORef out_r $! addToUFM_Directly out uniq (j, f)
           return (fromIntegral j :: Word32)

data FSTable = FSTable
  { fs_tab_next :: !FastMutInt
  , fs_tab_map  :: !(IORef (UniqFM FastString (Int,FastString)))
  }

type SymbolTable = Array Int Name

putFS :: BinHandle -> FastString -> IO ()
putFS bh fs = putBS bh $ bytesFS fs

getFS :: BinHandle -> IO FastString
getFS bh = do
  l  <- get bh :: IO Int
  getPrim bh l (\src -> pure $! mkFastStringBytes src l )

putByteString :: BinHandle -> ByteString -> IO ()
putByteString bh bs =
  BS.unsafeUseAsCStringLen bs $ \(ptr, l) -> do
    putPrim bh l (\op -> copyBytes op (castPtr ptr) l)

getByteString :: BinHandle -> Int -> IO ByteString
getByteString bh l =
  BS.create l $ \dest -> do
    getPrim bh l (\src -> copyBytes dest src l)

putBS :: BinHandle -> ByteString -> IO ()
putBS bh bs =
  BS.unsafeUseAsCStringLen bs $ \(ptr, l) -> do
    put_ bh l
    putPrim bh l (\op -> copyBytes op (castPtr ptr) l)

getBS :: BinHandle -> IO ByteString
getBS bh = do
  l <- get bh :: IO Int
  BS.create l $ \dest -> do
    getPrim bh l (\src -> copyBytes dest src l)

instance Binary ByteString where
  put_ bh f = putBS bh f
  get bh = getBS bh

instance Binary FastString where
  put_ bh f =
    case getUserData bh of
        UserData { ud_put_fs = put_fs } -> put_fs bh f

  get bh =
    case getUserData bh of
        UserData { ud_get_fs = get_fs } -> get_fs bh

deriving instance Binary NonDetFastString
deriving instance Binary LexicalFastString

instance Binary Fingerprint where
  put_ h (Fingerprint w1 w2) = do put_ h w1; put_ h w2
  get  h = do w1 <- get h; w2 <- get h; return (Fingerprint w1 w2)

instance Binary ModuleName where
  put_ bh (ModuleName fs) = put_ bh fs
  get bh = do fs <- get bh; return (ModuleName fs)

newtype BinLocated a = BinLocated { unBinLocated :: Located a }

instance Binary a => Binary (BinLocated a) where
    put_ bh (BinLocated (L l x)) = do
            put_ bh $ BinSrcSpan l
            put_ bh x

    get bh = do
            l <- unBinSrcSpan <$> get bh
            x <- get bh
            return $ BinLocated (L l x)

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

instance (Binary v) => Binary (IntMap v) where
  put_ bh m = put_ bh (IntMap.toList m)
  get bh = IntMap.fromList <$> get bh
