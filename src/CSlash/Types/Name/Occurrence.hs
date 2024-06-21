{-# LANGUAGE MagicHash #-}

module CSlash.Types.Name.Occurrence where

import CSlash.Builtin.Uniques
import CSlash.Data.FastString
import CSlash.Types.Unique
import CSlash.Utils.Outputable

import qualified Data.Semigroup as S
import GHC.Exts ( Int(I#), dataToTag# )

data NameSpace
  = VarName
  | TvName
  | KvName
  deriving Eq

instance Ord NameSpace where
  compare ns1 ns2 = compare (I# (dataToTag# ns1)) (I# (dataToTag# ns2))

instance Uniquable NameSpace where
  getUnique VarName = varNSUnique
  getUnique TvName = tvNSUnique
  getUnique KvName = kvNSUnique

varName :: NameSpace
varName = VarName

tvName :: NameSpace
tvName = TvName

kvName :: NameSpace
kvName = KvName

data OccName = OccName
  { occNameSpace :: !NameSpace
  , occNameFS :: !FastString
  }

instance Eq OccName where
  (OccName sp1 s1) == (OccName sp2 s2) = s1 == s2 && sp1 == sp2

instance Ord OccName where
  compare (OccName sp1 s1) (OccName sp2 s2) =
    lexicalCompareFS s1 s2 S.<> compare sp1 sp2

occNameMangledFS :: OccName -> FastString
occNameMangledFS (OccName _ns fs) = fs
  -- case ns of
  --   FldName con -> concatFS [fsLit "$fld:", con, ":", fs]
  --   _ -> fs

pprNameSpaceBrief :: NameSpace -> SDoc
pprNameSpaceBrief VarName = char 'v'
pprNameSpaceBrief TvName = text "tv"
pprNameSpaceBrief KvName = text "kv"

mkOccName :: NameSpace -> String -> OccName
mkOccName occ_sp str = OccName occ_sp (mkFastString str)

mkOccNameFS :: NameSpace -> FastString -> OccName
mkOccNameFS occ_sp fs = OccName occ_sp fs

mkVarOcc :: String -> OccName
mkVarOcc s = mkOccName varName s

mkVarOccFS :: FastString -> OccName
mkVarOccFS fs = mkOccNameFS varName fs

class HasOccName name where
  occName :: name -> OccName
