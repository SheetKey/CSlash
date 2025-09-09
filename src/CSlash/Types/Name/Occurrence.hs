{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MagicHash #-}

module CSlash.Types.Name.Occurrence
  ( module CSlash.Types.Name.Occurrence
  , FastStringEnv, emptyFsEnv, lookupFsEnv, extendFsEnv, mkFsEnv
  ) where

import Prelude hiding ((<>))

import CSlash.Builtin.Uniques
import CSlash.Data.FastString
import CSlash.Data.FastString.Env
import CSlash.Types.Unique
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.Set
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

isTermVarNameSpace :: NameSpace -> Bool
isTermVarNameSpace VarName = True
isTermVarNameSpace _ = False

isVarNameSpace :: NameSpace -> Bool
isVarNameSpace TvName = True
isVarNameSpace KvName = True
isVarNameSpace VarName = True
isVarNameSpace _ = False

isUnknownNameSpace :: NameSpace -> Bool
isUnknownNameSpace UNKNOWN_NS = True
isUnknownNameSpace _ = False

isValNameSpace :: NameSpace -> Bool
isValNameSpace DataName = True
isValNameSpace VarName = True
isValNameSpace _ = False

pprNameSpace :: NameSpace -> SDoc
pprNameSpace VarName = text "variable"
pprNameSpace TvName = text "type variable"
pprNameSpace KvName = text "kind variable"
pprNameSpace TcClsName = text "type constructor or class"
pprNameSpace DataName = text "data constructor"
pprNameSpace UNKNOWN_NS = text "UNKNOWN_NS"

pprNonVarNameSpace :: NameSpace -> SDoc
pprNonVarNameSpace VarName = empty
pprNonVarNameSpace ns = pprNameSpace ns

pprNameSpaceBrief :: NameSpace -> SDoc
pprNameSpaceBrief VarName = char 'v'
pprNameSpaceBrief TvName = text "tv"
pprNameSpaceBrief KvName = text "kv"
pprNameSpaceBrief TcClsName = text "tc"
pprNameSpaceBrief DataName = text "dc"
pprNameSpaceBrief UNKNOWN_NS = text "UK_NS"

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

mkKiVarOcc :: String -> OccName
mkKiVarOcc = mkOccName kvName

mkKiVarOccFS :: FastString -> OccName
mkKiVarOccFS fs = mkOccNameFS kvName fs

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

lookupOccEnv_AllNameSpaces :: OccEnv a -> OccName -> [a]
lookupOccEnv_AllNameSpaces (MkOccEnv as) (OccName _ s)
  = case lookupFsEnv as s of
      Nothing -> []
      Just r -> nonDetEltsUFM r

mkOccEnv :: [(OccName, a)] -> OccEnv a
mkOccEnv = extendOccEnvList emptyOccEnv

mkOccEnv_C :: (a -> a -> a) -> [(OccName, a)] -> OccEnv a
mkOccEnv_C f elts = MkOccEnv $ foldl' g emptyFsEnv elts
  where g env (OccName ns s, a) = extendFsEnv_C (plusUFM_C $ flip f) env s (unitUFM ns a)

elemOccEnv :: OccName -> OccEnv a -> Bool
elemOccEnv (OccName ns s) (MkOccEnv as) = case lookupFsEnv as s of
  Nothing -> False
  Just m -> ns `elemUFM` m

nonDetFoldOccEnv :: (a -> b -> b) -> b -> OccEnv a -> b
nonDetFoldOccEnv f b0 (MkOccEnv as) =
  nonDetFoldFsEnv (flip $ nonDetFoldUFM f) b0 as

nonDetOccEnvElts :: OccEnv a -> [a]
nonDetOccEnvElts = nonDetFoldOccEnv (:) []

plusOccEnv_C :: (a -> a -> a) -> OccEnv a -> OccEnv a -> OccEnv a
plusOccEnv_C f (MkOccEnv env1) (MkOccEnv env2) = MkOccEnv $ plusFsEnv_C (plusUFM_C f) env1 env2

extendOccEnv_Acc
  :: forall a b
  .  (a -> b -> b)
  -> (a -> b)
  -> OccEnv b
  -> OccName
  -> a
  -> OccEnv b
extendOccEnv_Acc f g (MkOccEnv env) (OccName ns s)
  = MkOccEnv . extendFsEnv_Acc f' g' env s
  where
    f' :: a -> UniqFM NameSpace b -> UniqFM NameSpace b
    f' a bs = alterUFM (Just . \case { Nothing -> g a; Just b -> f a b }) bs ns
    g' a = unitUFM ns (g a)

instance Outputable a => Outputable (OccEnv a) where
  ppr x = pprOccEnv ppr x

pprOccEnv :: (a -> SDoc) -> OccEnv a -> SDoc
pprOccEnv ppr_elt (MkOccEnv env) = brackets $ fsep $ punctuate comma $
  [ ppr uq <+> text ":->" <+> ppr_elt elt
  | (uq, elts) <- nonDetUFMToList env
  , elt <- nonDetEltsUFM elts ]

--------------------------------------------------------------------------------

newtype OccSet = OccSet (FastStringEnv (UniqSet NameSpace))

emptyOccSet :: OccSet
emptyOccSet = OccSet emptyFsEnv

unitOccSet :: OccName -> OccSet
unitOccSet (OccName ns s) = OccSet $ unitFsEnv s (unitUniqSet ns)

mkOccSet :: [OccName] -> OccSet
mkOccSet = extendOccSetList emptyOccSet

extendOccSet :: OccSet -> OccName -> OccSet
extendOccSet (OccSet occs) (OccName ns s) = OccSet $ extendFsEnv occs s (unitUniqSet ns)

extendOccSetList :: OccSet -> [OccName] -> OccSet
extendOccSetList = foldl' extendOccSet

unionOccSets :: OccSet -> OccSet -> OccSet
unionOccSets (OccSet xs) (OccSet ys) = OccSet $ plusFsEnv_C unionUniqSets xs ys

unionManyOccSets :: [OccSet] -> OccSet
unionManyOccSets = foldl' unionOccSets emptyOccSet

elemOccSet :: OccName -> OccSet -> Bool
elemOccSet (OccName ns s) (OccSet occs) = maybe False (elementOfUniqSet ns) $ lookupFsEnv occs s

isEmptyOccSet :: OccSet -> Bool
isEmptyOccSet (OccSet occs) = isNullUFM occs

{- *********************************************************************
*                                                                      *
            Predicates and taking them apart
*                                                                      *
********************************************************************* -}

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
  DataName -> isLexConSym s
  UNKNOWN_NS -> False

isConOccFS :: OccName -> Bool
isConOccFS (OccName _ s) = isLexCon s

{- *********************************************************************
*                                                                      *
            Predicates and taking them apart
*                                                                      *
********************************************************************* -}

setOccNameSpace :: NameSpace -> OccName -> OccName
setOccNameSpace sp (OccName _ occ) = OccName sp occ

startsWithUnderscore :: OccName -> Bool
startsWithUnderscore occ = case unpackFS (occNameFS occ) of
  '_':_ -> True
  _ -> False

{- *********************************************************************
*                                                                      *
            Making system names
*                                                                      *
********************************************************************* -}

mk_deriv :: NameSpace -> FastString -> [FastString] -> OccName
mk_deriv occ_sp sys_prefix str = mkOccNameFS occ_sp (concatFS $ sys_prefix : str)

isDerivedOccName :: OccName -> Bool
isDerivedOccName occ = case occNameString occ of
  '$':c:_ | isAlphaNum c -> True
  c:':':_ | isAlphaNum c -> True
  _ -> False

mkDataConOcc :: OccName -> OccName
mkDataConOcc = mk_simple_deriv varName "$W"

mk_simple_deriv :: NameSpace -> FastString -> OccName -> OccName
mk_simple_deriv sp px occ = mk_deriv sp px [occNameFS occ]

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

delTidyOccEnvList :: TidyOccEnv -> [OccName] -> TidyOccEnv
delTidyOccEnvList env occs = env `delListFromUFM` map occNameFS occs

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

trimTidyOccEnv :: TidyOccEnv -> [OccName] -> TidyOccEnv
trimTidyOccEnv env vs = foldl' add emptyUFM vs
  where
    add so_far (OccName _ fs) = case lookupUFM env fs of
                                  Just n -> addToUFM so_far fs n
                                  Nothing -> so_far

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
