{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MagicHash #-}

module CSlash.Types.Name.Occurrence where

import Prelude hiding ((<>))

import CSlash.Builtin.Uniques
import CSlash.Data.FastString
import CSlash.Data.FastString.Env
import CSlash.Types.Unique
import CSlash.Types.Unique.FM
import CSlash.Utils.Outputable
import CSlash.Utils.Lexeme
import CSlash.Utils.Misc

import qualified Data.Semigroup as S
import GHC.Exts ( Int(I#), dataToTag# )

import Control.DeepSeq
import Data.Data

data NameSpace
  = VarName
  | TvName
  | KvName
  | TcClsName
  deriving Eq

instance Ord NameSpace where
  compare ns1 ns2 = compare (I# (dataToTag# ns1)) (I# (dataToTag# ns2))

instance Uniquable NameSpace where
  getUnique VarName = varNSUnique
  getUnique TvName = tvNSUnique
  getUnique KvName = kvNSUnique
  getUnique TcClsName = tcNSUnique

varName :: NameSpace
varName = VarName

tvName :: NameSpace
tvName = TvName

kvName :: NameSpace
kvName = KvName

tcName :: NameSpace
tcName = TcClsName

tcClsName :: NameSpace
tcClsName = TcClsName

pprNameSpace :: NameSpace -> SDoc
pprNameSpace VarName = text "variable"
pprNameSpace TvName = text "type variable"
pprNameSpace KvName = text "kind variable"
pprNameSpace TcClsName = text "type constructor or class"

pprNameSpaceBrief :: NameSpace -> SDoc
pprNameSpaceBrief VarName = char 'v'
pprNameSpaceBrief TvName = text "tv"
pprNameSpaceBrief KvName = text "kv"
pprNameSpaceBrief TcClsName = text "tc"

data OccName = OccName
  { occNameSpace :: !NameSpace
  , occNameFS :: !FastString
  }

instance Eq OccName where
  (OccName sp1 s1) == (OccName sp2 s2) = s1 == s2 && sp1 == sp2

instance Ord OccName where
  compare (OccName sp1 s1) (OccName sp2 s2) =
    lexicalCompareFS s1 s2 S.<> compare sp1 sp2

instance Data OccName where
  toConstr _ = abstractConstr "OccName"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "OccName"

instance HasOccName OccName where
  occName = id

instance NFData OccName where
  rnf x = x `seq` ()

instance Outputable OccName where
  ppr = pprOccName

instance OutputableBndr OccName where
  pprBndr _ = ppr
  pprInfixOcc n = pprInfixVar (isSymOcc n) (ppr n)
  pprPrefixOcc n = pprPrefixVar (isSymOcc n) (ppr n)

pprOccName :: IsLine doc => OccName -> doc
pprOccName (OccName sp occ)
  = docWithStyle (ztext (zEncodeFS occ))
    (\ _ -> ftext occ <> whenPprDebug (braces (pprNameSpaceBrief sp)))

occNameMangledFS :: OccName -> FastString
occNameMangledFS (OccName _ns fs) = fs
  -- case ns of
  --   FldName con -> concatFS [fsLit "$fld:", con, ":", fs]
  --   _ -> fs

mkOccName :: NameSpace -> String -> OccName
mkOccName occ_sp str = OccName occ_sp (mkFastString str)

mkOccNameFS :: NameSpace -> FastString -> OccName
mkOccNameFS occ_sp fs = OccName occ_sp fs

mkVarOcc :: String -> OccName
mkVarOcc s = mkOccName varName s

mkVarOccFS :: FastString -> OccName
mkVarOccFS fs = mkOccNameFS varName fs

mkTyVarOcc :: String -> OccName
mkTyVarOcc = mkOccName tvName

mkTyVarOccFS :: FastString -> OccName
mkTyVarOccFS fs = mkOccNameFS tvName fs

mkKdVarOcc :: String -> OccName
mkKdVarOcc = mkOccName kvName

mkKdVarOccFS :: FastString -> OccName
mkKdVarOccFS fs = mkOccNameFS kvName fs

mkTcOcc :: String -> OccName
mkTcOcc = mkOccName tcName

mkTcOccFS :: FastString -> OccName
mkTcOccFS = mkOccNameFS tcName

class HasOccName name where
  occName :: name -> OccName

newtype OccEnv a = MkOccEnv (FastStringEnv (UniqFM NameSpace a))
  deriving Functor

emptyOccEnv :: OccEnv a
emptyOccEnv = MkOccEnv emptyFsEnv

extendOccEnv :: OccEnv a -> OccName -> a -> OccEnv a
extendOccEnv (MkOccEnv as) (OccName ns s) a =
  MkOccEnv $ extendFsEnv_C plusUFM as s (unitUFM ns a)

extendOccEnvList :: OccEnv a -> [(OccName, a)] -> OccEnv a
extendOccEnvList = foldl' $ \ env (occ, a) -> extendOccEnv env occ a

lookupOccEnv :: OccEnv a -> OccName -> Maybe a
lookupOccEnv (MkOccEnv as) (OccName ns s) = do
  m <- lookupFsEnv as s
  lookupUFM m ns

mkOccEnv :: [(OccName, a)] -> OccEnv a
mkOccEnv = extendOccEnvList emptyOccEnv

occNameString :: OccName -> String
occNameString (OccName _ s) = unpackFS s

isVarOcc :: OccName -> Bool
isVarOcc (OccName VarName _) = True
isVarOcc _ = False

isTvOcc :: OccName -> Bool
isTvOcc (OccName TvName _) = True
isTvOcc _ = False

isKvOcc :: OccName -> Bool
isKvOcc (OccName KvName _) = True
isKvOcc _ = False

isTcOcc :: OccName -> Bool
isTcOcc (OccName TcClsName _) = True
isTcOcc _ = False

isValOcc :: OccName -> Bool
isValOcc (OccName VarName _) = True
isValOcc _ = False

isSymOcc :: OccName -> Bool
isSymOcc (OccName ns s) = case ns of
  TcClsName -> isLexSym s
  VarName -> isLexSym s
  TvName -> isLexSym s
