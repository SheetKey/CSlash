{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Types.Name.Env (
        NameEnv,

        mkNameEnv, mkNameEnvWith,
        fromUniqMap,
        emptyNameEnv, isEmptyNameEnv,
        unitNameEnv, nonDetNameEnvElts,
        extendNameEnv_C, extendNameEnv_Acc, extendNameEnv,
        extendNameEnvList, extendNameEnvList_C,
        filterNameEnv, anyNameEnv,
        mapMaybeNameEnv,
        extendNameEnvListWith,
        plusNameEnv, plusNameEnv_C, plusNameEnv_CD, plusNameEnv_CD2, alterNameEnv,
        plusNameEnvList, plusNameEnvListWith,
        lookupNameEnv, lookupNameEnv_NF, delFromNameEnv, delListFromNameEnv,
        elemNameEnv, mapNameEnv, disjointNameEnv,
        seqEltsNameEnv,

        DNameEnv,

        emptyDNameEnv,
        isEmptyDNameEnv,
        lookupDNameEnv,
        delFromDNameEnv, filterDNameEnv,
        mapDNameEnv,
        adjustDNameEnv, alterDNameEnv, extendDNameEnv,
        eltsDNameEnv, extendDNameEnv_C,
        plusDNameEnv_C,
        foldDNameEnv,
        nonDetStrictFoldDNameEnv,

        depAnal
    ) where

import CSlash.Data.Graph.Directed
import CSlash.Types.Name
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.DFM
import CSlash.Types.Unique.Map
import CSlash.Data.Maybe

depAnal :: forall node .
           (node -> [Name])
        -> (node -> [Name])
        -> [node]
        -> [SCC node]
depAnal get_defs get_uses nodes
  = stronglyConnCompFromEdgedVerticesUniq graph_nodes
  where
    graph_nodes = (map mk_node keyed_nodes) :: [Node Int node]
    keyed_nodes = nodes `zip` [(1::Int)..]
    mk_node (node, key) =
      let !edges = (mapMaybe (lookupNameEnv key_map) (get_uses node))
      in DigraphNode node key edges

    key_map :: NameEnv Int   
    key_map = mkNameEnv [(name,key) | (node, key) <- keyed_nodes, name <- get_defs node]

type NameEnv a = UniqFM Name a       

emptyNameEnv       :: NameEnv a
isEmptyNameEnv     :: NameEnv a -> Bool
mkNameEnv          :: [(Name,a)] -> NameEnv a
mkNameEnvWith      :: (a -> Name) -> [a] -> NameEnv a
fromUniqMap        :: UniqMap Name a -> NameEnv a
nonDetNameEnvElts  :: NameEnv a -> [a]
alterNameEnv       :: (Maybe a-> Maybe a) -> NameEnv a -> Name -> NameEnv a
extendNameEnv_C    :: (a->a->a) -> NameEnv a -> Name -> a -> NameEnv a
extendNameEnv_Acc  :: (a->b->b) -> (a->b) -> NameEnv b -> Name -> a -> NameEnv b
extendNameEnv      :: NameEnv a -> Name -> a -> NameEnv a
plusNameEnv        :: NameEnv a -> NameEnv a -> NameEnv a
plusNameEnv_C      :: (a->a->a) -> NameEnv a -> NameEnv a -> NameEnv a
plusNameEnv_CD     :: (a->a->a) -> NameEnv a -> a -> NameEnv a -> a -> NameEnv a
plusNameEnv_CD2    :: (Maybe a->Maybe a->a) -> NameEnv a -> NameEnv a -> NameEnv a
plusNameEnvList    :: [NameEnv a] -> NameEnv a
plusNameEnvListWith :: (a->a->a) -> [NameEnv a] -> NameEnv a
extendNameEnvList  :: NameEnv a -> [(Name,a)] -> NameEnv a
extendNameEnvListWith :: (a -> Name) -> NameEnv a -> [a] -> NameEnv a
extendNameEnvList_C :: (a->a->a) -> NameEnv a -> [(Name,a)] -> NameEnv a
delFromNameEnv     :: NameEnv a -> Name -> NameEnv a
delListFromNameEnv :: NameEnv a -> [Name] -> NameEnv a
elemNameEnv        :: Name -> NameEnv a -> Bool
unitNameEnv        :: Name -> a -> NameEnv a
lookupNameEnv      :: NameEnv a -> Name -> Maybe a
lookupNameEnv_NF   :: NameEnv a -> Name -> a
filterNameEnv      :: (elt -> Bool) -> NameEnv elt -> NameEnv elt
mapMaybeNameEnv    :: (a -> Maybe b) -> NameEnv a -> NameEnv b
anyNameEnv         :: (elt -> Bool) -> NameEnv elt -> Bool
mapNameEnv         :: (elt1 -> elt2) -> NameEnv elt1 -> NameEnv elt2
disjointNameEnv    :: NameEnv a -> NameEnv a -> Bool
seqEltsNameEnv     :: (elt -> ()) -> NameEnv elt -> ()

nonDetNameEnvElts x         = nonDetEltsUFM x
emptyNameEnv          = emptyUFM
isEmptyNameEnv        = isNullUFM
unitNameEnv x y       = unitUFM x y
extendNameEnv x y z   = addToUFM x y z
extendNameEnvList x l = addListToUFM x l
extendNameEnvListWith f x l = addListToUFM x (map (\a -> (f a, a)) l)
lookupNameEnv x y     = lookupUFM x y
alterNameEnv          = alterUFM
mkNameEnv     l       = listToUFM l
mkNameEnvWith f       = mkNameEnv . map (\a -> (f a, a))
fromUniqMap           = mapUFM snd . getUniqMap
elemNameEnv x y          = elemUFM x y
plusNameEnv x y          = plusUFM x y
plusNameEnv_C f x y      = plusUFM_C f x y
{-# INLINE plusNameEnv_CD #-}
plusNameEnv_CD f x d y b = plusUFM_CD f x d y b
plusNameEnv_CD2 f x y    = plusUFM_CD2 f x y
{-# INLINE plusNameEnvList #-}
plusNameEnvList xs       = plusUFMList xs
{-# INLINE plusNameEnvListWith #-}
plusNameEnvListWith f xs = plusUFMListWith f xs
extendNameEnv_C f x y z  = addToUFM_C f x y z
mapNameEnv f x           = mapUFM f x
extendNameEnv_Acc x y z a b  = addToUFM_Acc x y z a b
extendNameEnvList_C x y z = addListToUFM_C x y z
delFromNameEnv x y      = delFromUFM x y
delListFromNameEnv x y  = delListFromUFM x y
filterNameEnv x y       = filterUFM x y
mapMaybeNameEnv x y     = mapMaybeUFM x y
anyNameEnv f x          = nonDetFoldUFM ((||) . f) False x
disjointNameEnv x y     = disjointUFM x y
seqEltsNameEnv seqElt x = seqEltsUFM seqElt x

lookupNameEnv_NF env n = expectJust "lookupNameEnv_NF" (lookupNameEnv env n)

type DNameEnv a = UniqDFM Name a

emptyDNameEnv :: DNameEnv a
emptyDNameEnv = emptyUDFM

isEmptyDNameEnv :: DNameEnv a -> Bool
isEmptyDNameEnv = isNullUDFM

lookupDNameEnv :: DNameEnv a -> Name -> Maybe a
lookupDNameEnv = lookupUDFM

delFromDNameEnv :: DNameEnv a -> Name -> DNameEnv a
delFromDNameEnv = delFromUDFM

filterDNameEnv :: (a -> Bool) -> DNameEnv a -> DNameEnv a
filterDNameEnv = filterUDFM

mapDNameEnv :: (a -> b) -> DNameEnv a -> DNameEnv b
mapDNameEnv = mapUDFM

adjustDNameEnv :: (a -> a) -> DNameEnv a -> Name -> DNameEnv a
adjustDNameEnv = adjustUDFM

alterDNameEnv :: (Maybe a -> Maybe a) -> DNameEnv a -> Name -> DNameEnv a
alterDNameEnv = alterUDFM

extendDNameEnv :: DNameEnv a -> Name -> a -> DNameEnv a
extendDNameEnv = addToUDFM

extendDNameEnv_C :: (a -> a -> a) -> DNameEnv a -> Name -> a -> DNameEnv a
extendDNameEnv_C = addToUDFM_C

eltsDNameEnv :: DNameEnv a -> [a]
eltsDNameEnv = eltsUDFM

foldDNameEnv :: (a -> b -> b) -> b -> DNameEnv a -> b
foldDNameEnv = foldUDFM

plusDNameEnv_C :: (elt -> elt -> elt) -> DNameEnv elt -> DNameEnv elt -> DNameEnv elt
plusDNameEnv_C = plusUDFM_C

nonDetStrictFoldDNameEnv :: (a -> b -> b) -> b -> DNameEnv a -> b
nonDetStrictFoldDNameEnv = nonDetStrictFoldUDFM
