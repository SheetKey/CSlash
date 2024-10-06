{-# LANGUAGE ScopedTypeVariables #-}

module CSlash.Iface.Binary where

import Prelude hiding ((<>))

-- import GHC.Tc.Utils.Monad
import CSlash.Builtin.Utils   ( isKnownKeyName, lookupKnownKeyName )
import CSlash.Unit
import CSlash.Unit.Module.ModIface
import CSlash.Types.Name
import CSlash.Platform.Profile
import CSlash.Types.Unique.FM
import CSlash.Utils.Panic
import CSlash.Utils.Binary as Binary
import CSlash.Data.FastMutInt
import CSlash.Types.Unique
import CSlash.Utils.Outputable
import CSlash.Types.Name.Cache
import CSlash.Types.SrcLoc
import CSlash.Platform
import CSlash.Settings.Constants
import CSlash.Utils.Fingerprint

import Data.Array
import Data.Array.IO
import Data.Array.Unsafe
import Data.Char
import Data.Word
import Data.IORef
import Control.Monad
import Data.Bits ((.&.), shiftR)

data CheckHiWay = CheckHiWay | IgnoreHiWay
  deriving Eq

data TraceBinIFace
  = TraceBinIFace (SDoc -> IO ())
  | QuietBinIFace

readBinIfaceHeader
  :: Profile
  -> CheckHiWay
  -> TraceBinIFace
  -> FilePath
  -> IO (Fingerprint, BinHandle)
readBinIfaceHeader profile checkHiWay traceBinIFace hi_path = do
  let platform = profilePlatform profile

      wantedGot :: String -> a -> a -> (a -> SDoc) -> IO ()
      wantedGot what wanted got ppr' =
        case traceBinIFace of
          QuietBinIFace -> return ()
          TraceBinIFace printer -> printer $
            text what <> text ": " <>
            vcat [ text "Wanted " <> ppr' wanted <> text ","
                 , text "got    " <> ppr' got
                 ]

      errorOnMismatch :: (Eq a, Show a) => String -> a -> a -> IO ()
      errorOnMismatch what wanted got =
        when (wanted /= got) $ throwCsExceptionIO $ ProgramError
        (what ++ " (wanted " ++ show wanted
              ++ ", got " ++ show got ++ ")")

  bh <- Binary.readBinMem hi_path
                
  magic <- get bh
  wantedGot "Magic" (binaryInterfaceMagic platform) magic (ppr . unFixedLength)
  errorOnMismatch "magic number mismatch: old/corrupt interface file?"
    (unFixedLength $ binaryInterfaceMagic platform) (unFixedLength magic)

  check_ver <- get bh
  let our_ver = show hiVersion
  wantedGot "Version" our_ver check_ver text
  errorOnMismatch "mismatched interface file versions" our_ver check_ver

  check_tag <- get bh
  let tag = profileBuildTag profile
  wantedGot "Way" tag check_tag text
  when (checkHiWay == CheckHiWay) $
    errorOnMismatch "mismatched interface file profile tag" tag check_tag

  src_hash <- get bh
  pure (src_hash, bh)

readBinIface
  :: Profile
  -> NameCache
  -> CheckHiWay
  -> TraceBinIFace
  -> FilePath
  -> IO ModIface
readBinIface profile name_cache checkHiWay traceBinIface hi_path = do
  (src_hash, bh) <- readBinIfaceHeader profile checkHiWay traceBinIface hi_path

  mod_iface <- getWithUserData name_cache bh

  return mod_iface { mi_src_hash = src_hash }

getWithUserData :: Binary a => NameCache -> BinHandle -> IO a
getWithUserData name_cache bh = do
  bh <- getTables name_cache bh
  get bh

getTables :: NameCache -> BinHandle -> IO BinHandle
getTables name_cache bh = do
  dict <- Binary.forwardGet bh (getDictionary bh)

  let bh_fs = setUserData bh $ newReadState (error "getSymtabName") (getDictFastString dict)

  symtab <- Binary.forwardGet bh_fs (getSymbolTable bh_fs name_cache)

  return $ setUserData bh $ newReadState (getSymtabName name_cache dict symtab)
                                         (getDictFastString dict)

binaryInterfaceMagic :: Platform -> FixedLengthEncoding Word32
binaryInterfaceMagic platform
  | target32Bit platform = FixedLengthEncoding 0x1face
  | otherwise            = FixedLengthEncoding 0x1face64


-- -----------------------------------------------------------------------------
-- The symbol table
--

getSymbolTable :: BinHandle -> NameCache -> IO SymbolTable
getSymbolTable bh name_cache = do
  sz <- get bh :: IO Int

  updateNameCache' name_cache $ \cache0 -> do
    mut_arr <- newArray_ (0, sz-1) :: IO (IOArray Int Name)
    cache <- foldGet' (fromIntegral sz) bh cache0 $ \i (uid, mod_name, occ) cache -> 
      let mod = mkModule uid mod_name
      in case lookupOrigNameCache cache mod occ of
           Just name -> do
             writeArray mut_arr (fromIntegral i) name
             return cache
           Nothing -> do
             uniq <- takeUniqFromNameCache name_cache
             let name = mkExternalName uniq mod occ noSrcSpan
                 new_cache = extendOrigNameCache cache mod occ name
             writeArray mut_arr (fromIntegral i) name
             return new_cache
    arr <- unsafeFreeze mut_arr
    return (cache, arr)

getSymtabName
  :: NameCache
  -> Dictionary
  -> SymbolTable
  -> BinHandle
  -> IO Name
getSymtabName _ _ symtab bh = do
  i :: Word32 <- get bh
  case i .&. 0xC0000000 of
    0x00000000 -> return $! symtab ! fromIntegral i

    0x80000000 ->
      let tag = chr (fromIntegral ((i .&. 0x3FC00000) `shiftR` 22))
          ix  = fromIntegral i .&. 0x003FFFFF
          u   = mkUnique tag ix
      in return $! case lookupKnownKeyName u of
                     Nothing -> pprPanic "getSymtabName:unknown known-key unique"
                                         (ppr i $$ ppr u $$ char tag $$ ppr ix)
                     Just n  -> n
    _ -> pprPanic "getSymtabName:unknown name tag" (ppr i)
