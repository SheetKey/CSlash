module CSlash.Iface.Recomp.Binary where

import CSlash.Utils.Fingerprint
import CSlash.Utils.Binary
import CSlash.Types.Name
import CSlash.Utils.Panic.Plain
import CSlash.Iface.Type (putIfaceType)

fingerprintBinMem :: WriteBinHandle -> IO Fingerprint
fingerprintBinMem bh = withBinBuffer bh f
  where
    f bs = let fp = fingerprintByteString bs
           in fp `seq` return fp

computeFingerprint :: (Binary a) => (WriteBinHandle -> Name -> IO ()) -> a -> IO Fingerprint
computeFingerprint put_nonbinding_name a = do
    bh <- fmap set_user_data $ openBinMem (3*1024)
    put_ bh a
    fingerprintBinMem bh
  where
    set_user_data bh = setWriterUserData bh $ mkWriterUserData
      [ mkSomeBinaryWriter $ mkWriter putIfaceType
      , mkSomeBinaryWriter $ mkWriter put_nonbinding_name
      , mkSomeBinaryWriter $ simpleBindingNameWriter $ mkWriter putNameLiterally
      , mkSomeBinaryWriter $ mkWriter putFS
      ]

putNameLiterally :: WriteBinHandle -> Name -> IO ()
putNameLiterally bh name = assert (isExternalName name) $ do
  put_ bh $! nameModule name
  put_ bh $! nameOccName name
