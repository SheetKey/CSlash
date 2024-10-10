{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MagicHash #-}

module CSlash.Types.Name.Occurrence
  ( module CSlash.Types.Name.Occurrence
  , FastStringEnv
  ) where

import Prelude hiding ((<>))

import CSlash.Builtin.Uniques
import CSlash.Data.FastString
import CSlash.Data.FastString.Env
import CSlash.Types.Unique
import CSlash.Types.Unique.FM
import CSlash.Utils.Outputable
import CSlash.Utils.Lexeme
import CSlash.Utils.Binary
import CSlash.Utils.Misc

import qualified Data.Semigroup as S
import GHC.Exts ( Int(I#), dataToTag# )

import Control.DeepSeq
import Data.Char
import Data.Data

data NameSpace
  = VarName
  | TvName
  | KvName
  | TcClsName
  | DataName
  | UNKNOWN_NS
  deriving Eq

instance Ord NameSpace where
  compare ns1 ns2 = compare (I# (dataToTag# ns1)) (I# (dataToTag# ns2))

instance Uniquable NameSpace where
  getUnique VarName = varNSUnique
  getUnique TvName = tvNSUnique
  getUnique KvName = kvNSUnique
  getUnique TcClsName = tcNSUnique
  getUnique DataName = dataNSUnique
  getUnique UNKNOWN_NS = unknownNSUnique

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

dataName :: NameSpace
dataName = DataName

isDataConNameSpace :: NameSpace -> Bool
isDataConNameSpace DataName = True
isDataConNameSpace _ = False

isTcClsNameSpace :: NameSpace -> Bool
isTcClsNameSpace TcClsName = True
isTcClsNameSpace _ = False

isTvNameSpace :: NameSpace -> Bool
isTvNameSpace TvName = True
isTvNameSpace _ = False

isKvNameSpace :: NameSpace -> Bool
isKvNameSpace KvName = True
isKvNameSpace _ = False

isVarNameSpace :: NameSpace -> Bool
isVarNameSpace TvName = True
isVarNameSpace KvName = True
isVarNameSpace VarName = True
isVarNameSpace _ = False

isUnknownNameSpace :: NameSpace -> Bool
isUnknownNameSpace UNKNOWN_NS = True
isUnknownNameSpace _ = False

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

mkDataOcc :: String -> OccName
mkDataOcc = mkOccName dataName

mkDataOccFS :: FastString -> OccName
mkDataOccFS = mkOccNameFS dataName

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

mkUnknownOcc :: String -> OccName
mkUnknownOcc = mkOccName UNKNOWN_NS

mkUnknownOccFS :: FastString -> OccName
mkUnknownOccFS = mkOccNameFS UNKNOWN_NS

class HasOccName name where
  occName :: name -> OccName

newtype OccEnv a = MkOccEnv (FastStringEnv (UniqFM NameSpace a))
  deriving Functor

emptyOccEnv :: OccEnv a
emptyOccEnv = MkOccEnv emptyFsEnv

unitOccEnv :: OccName -> a -> OccEnv a
unitOccEnv (OccName ns s) a = MkOccEnv $ unitFsEnv s (unitUFM ns a)

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

isDataOcc :: OccName -> Bool
isDataOcc (OccName DataName _) = True
isDataOcc _ = False

isValOcc :: OccName -> Bool
isValOcc (OccName VarName _) = True
isValOcc _ = False

isUnknownOcc :: OccName -> Bool
isUnknownOcc (OccName UNKNOWN_NS _) = True
isUnknownOcc _ = False

isSymOcc :: OccName -> Bool
isSymOcc (OccName ns s) = case ns of
  VarName -> isLexSym s
  TvName -> isLexSym s
  KvName -> isLexKdSym s
  TcClsName -> isLexSym s

isConOccFS :: OccName -> Bool
isConOccFS (OccName _ s) = isLexCon s

{- *********************************************************************
*                                                                      *
            Predicates and taking them apart
*                                                                      *
********************************************************************* -}

setOccNameSpace :: NameSpace -> OccName -> OccName
setOccNameSpace sp (OccName _ occ) = OccName sp occ

{- *********************************************************************
*                                                                      *
            Making system names
*                                                                      *
********************************************************************* -}

mkDataConWorkerOcc :: OccName -> OccName
mkDataConWorkerOcc datacon_occ = setOccNameSpace varName datacon_occ

{- *********************************************************************
*                                                                      *
            Tidying them up
*                                                                      *
********************************************************************* -}

type TidyOccEnv = UniqFM FastString Int

emptyTidyOccEnv :: TidyOccEnv
emptyTidyOccEnv = emptyUFM

initTidyOccEnv :: [OccName] -> TidyOccEnv
initTidyOccEnv = foldl' add emptyUFM
  where
    add env (OccName _ fs) = addToUFM env fs 1

delTidyOccEnvList :: TidyOccEnv -> [FastString] -> TidyOccEnv
delTidyOccEnvList = delListFromUFM

avoidClashesOccEnv :: TidyOccEnv -> [OccName] -> TidyOccEnv
avoidClashesOccEnv env occs = go env emptyUFM occs
  where
    go env _ [] = env
    go env seenOnce ((OccName _ fs) : occs)
      | fs `elemUFM` env = go env seenOnce occs
      | fs `elemUFM` seenOnce = go (addToUFM env fs 1) seenOnce occs
      | otherwise = go env (addToUFM seenOnce fs ()) occs

tidyOccName :: TidyOccEnv -> OccName -> (TidyOccEnv, OccName)
tidyOccName env occ@(OccName occ_sp fs)
  | not (fs `elemUFM` env)
  = (addToUFM env fs 1, occ)
  | otherwise
  = case lookupUFM env base1 of
      Nothing -> (addToUFM env base1 2, OccName occ_sp base1)
      Just n -> find 1 n
  where
    base :: String
    base = dropWhileEndLE isDigit (unpackFS fs)
    base1 = mkFastString (base ++ "1")

    find !k !n
      = case elemUFM new_fs env of
          True -> find (k+1 :: Int) (n+k)
          False -> (new_env, OccName occ_sp new_fs)
      where
        new_fs = mkFastString (base ++ show n)
        new_env = addToUFM (addToUFM env new_fs 1) base1 (n+1)

{- *********************************************************************
*                                                                      *
                Binary instance
*                                                                      *
********************************************************************* -}

instance Binary NameSpace where
  put_ bh VarName = putByte bh 0
  put_ bh DataName = putByte bh 1
  put_ bh TvName = putByte bh 2
  put_ bh TcClsName = putByte bh 3
  put_ bh KvName = putByte bh 4
  put_ _ UNKNOWN_NS = error "put_ bh UNKNOWN_NS"
  get bh = do
    h <- getByte bh
    case h of
      0 -> return VarName
      1 -> return DataName
      2 -> return TvName
      3 -> return TcClsName
      _ -> return KvName

instance Binary OccName where
  put_ bh (OccName aa ab) = do
    put_ bh aa
    put_ bh ab
  get bh = do
    aa <- get bh
    ab <- get bh
    return (OccName aa ab)    
