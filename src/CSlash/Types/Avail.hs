{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Types.Avail where

import Prelude hiding ((<>))

import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set

import CSlash.Utils.Binary
-- import CSlash.Data.List.SetOps
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Constants (debugIsOn)

import Control.DeepSeq
import Data.Data ( Data )
import Data.Functor.Classes ( liftCompare )
import Data.List ( find )
import qualified Data.Semigroup as S

data AvailInfo
  = Avail Name
  | AvailTC Name [Name]
  deriving Data

type Avails = [AvailInfo]

availExportsDecl :: AvailInfo -> Bool
availExportsDecl (AvailTC ty_name names)
  | n : _ <- names = ty_name == n
  | otherwise = False
availExportsDecl _ = True

availSubordinateNames :: AvailInfo -> [Name]
availSubordinateNames (Avail{}) = []
availSubordinateNames avail@(AvailTC _ ns)
  | availExportsDecl avail = tail ns
  | otherwise = ns

-- -----------------------------------------------------------------------------
-- Operations on AvailInfo

availName :: AvailInfo -> Name
availName (Avail n) = n
availName (AvailTC n _) = n

availNames :: AvailInfo -> [Name]
availNames (Avail n) = [n]
availNames (AvailTC _ cs) = cs

-- -----------------------------------------------------------------------------
-- Printing

instance Outputable AvailInfo where
  ppr = pprAvail

pprAvail :: AvailInfo -> SDoc
pprAvail (Avail n) = ppr n
pprAvail (AvailTC n ns) = ppr n <> braces (pprWithCommas ppr ns)

instance Binary AvailInfo where
  put_ bh (Avail aa) = do
    putByte bh 0
    put_ bh aa
  put_ bh (AvailTC ab ac) = do
    putByte bh 1
    put_ bh ab
    put_ bh ac

  get bh = do
    h <- getByte bh
    case h of
      0 -> Avail <$> get bh
      1 -> AvailTC <$> get bh <*> get bh
      _ -> panic "invalid byte"
