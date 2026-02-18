module CSlash.Data.Graph.UnVar where

import CSlash.Cs.Pass

import CSlash.Types.Unique.FM( UniqFM, ufmToSet_Directly )
import CSlash.Types.Var.Id
import CSlash.Utils.Outputable
import CSlash.Types.Unique

import GHC.Word
import qualified GHC.Data.Word64Set as S

newtype UnVarSet = UnVarSet S.Word64Set
  deriving Eq

k :: Id Zk -> Word64
k v = getKey (getUnique v)

domUFMUnVarSet :: UniqFM key elt -> UnVarSet
domUFMUnVarSet ae = UnVarSet $ ufmToSet_Directly ae

emptyUnVarSet :: UnVarSet
emptyUnVarSet = UnVarSet S.empty

elemUnVarSet :: Id Zk -> UnVarSet -> Bool
elemUnVarSet v (UnVarSet s) = k v `S.member` s

isEmptyUnVarSet :: UnVarSet -> Bool
isEmptyUnVarSet (UnVarSet s) = S.null s

delUnVarSet :: UnVarSet -> Id Zk -> UnVarSet
delUnVarSet (UnVarSet s) v = UnVarSet $ k v `S.delete` s

delUnVarSetList :: UnVarSet -> [Id Zk] -> UnVarSet
delUnVarSetList s vs = s `minusUnVarSet` mkUnVarSet vs

minusUnVarSet :: UnVarSet -> UnVarSet -> UnVarSet
minusUnVarSet (UnVarSet s) (UnVarSet s') = UnVarSet $ s `S.difference` s'

sizeUnVarSet :: UnVarSet -> Int
sizeUnVarSet (UnVarSet s) = S.size s

mkUnVarSet :: [Id Zk] -> UnVarSet
mkUnVarSet vs = UnVarSet $ S.fromList $ map k vs

extendUnVarSet :: Id Zk -> UnVarSet -> UnVarSet
extendUnVarSet v (UnVarSet s) = UnVarSet $ S.insert (k v) s

unionUnVarSet :: UnVarSet -> UnVarSet -> UnVarSet
unionUnVarSet (UnVarSet set1) (UnVarSet set2) = UnVarSet (set1 `S.union` set2)

unionUnVarSets :: [UnVarSet] -> UnVarSet
unionUnVarSets = foldl' (flip unionUnVarSet) emptyUnVarSet

instance Outputable UnVarSet where
    ppr (UnVarSet s) = braces $
        hcat $ punctuate comma [ ppr (mkUniqueGrimily i) | i <- S.toList s]

data UnVarGraph = CBPG  !UnVarSet !UnVarSet
                | CG    !UnVarSet
                | Union UnVarGraph UnVarGraph
                | Del   !UnVarSet UnVarGraph

emptyUnVarGraph :: UnVarGraph
emptyUnVarGraph = CG emptyUnVarSet

unionUnVarGraph :: UnVarGraph -> UnVarGraph -> UnVarGraph
unionUnVarGraph a b
  | is_null a = b
  | is_null b = a
  | otherwise = Union a b

unionUnVarGraphs :: [UnVarGraph] -> UnVarGraph
unionUnVarGraphs = foldl' unionUnVarGraph emptyUnVarGraph

completeBipartiteGraph :: UnVarSet -> UnVarSet -> UnVarGraph
completeBipartiteGraph s1 s2 = prune $ CBPG s1 s2

completeGraph :: UnVarSet -> UnVarGraph
completeGraph s = prune $ CG s

neighbors :: UnVarGraph -> Id Zk -> UnVarSet
neighbors = go
  where
    go (Del d g) v
      | v `elemUnVarSet` d = emptyUnVarSet
      | otherwise = go g v `minusUnVarSet` d
    go (Union g1 g2) v = go g1 v `unionUnVarSet` go g2 v
    go (CG s) v = if v `elemUnVarSet` s then s else emptyUnVarSet
    go (CBPG s1 s2) v = (if v `elemUnVarSet` s1 then s2 else emptyUnVarSet) `unionUnVarSet`
                        (if v `elemUnVarSet` s2 then s1 else emptyUnVarSet)

hasLoopAt :: UnVarGraph -> Id Zk -> Bool
hasLoopAt = go
  where
    go (Del d g) v
      | v `elemUnVarSet` d = False
      | otherwise = go g v
    go (Union g1 g2) v = go g1 v || go g2 v
    go (CG s) v = v `elemUnVarSet` s
    go (CBPG s1 s2) v = v `elemUnVarSet` s1 && v `elemUnVarSet` s2

delNode :: UnVarGraph -> Id Zk -> UnVarGraph
delNode (Del d g) v = Del (extendUnVarSet v d) g
delNode g v
  | is_null g = emptyUnVarGraph
  | otherwise = Del (mkUnVarSet [v]) g

prune :: UnVarGraph -> UnVarGraph
prune = go emptyUnVarSet
  where
    go :: UnVarSet -> UnVarGraph -> UnVarGraph
    go dels (Del dels' g) = go (dels `unionUnVarSet` dels') g
    go dels (Union g1 g2)
      | is_null g1' = g2'
      | is_null g2' = g1'
      | otherwise   = Union g1' g2'
      where
        g1' = go dels g1
        g2' = go dels g2
    go dels (CG s)        = CG (s `minusUnVarSet` dels)
    go dels (CBPG s1 s2)  = CBPG (s1 `minusUnVarSet` dels) (s2 `minusUnVarSet` dels)

is_null :: UnVarGraph -> Bool
is_null (CBPG s1 s2) = isEmptyUnVarSet s1 || isEmptyUnVarSet s2
is_null (CG s) = isEmptyUnVarSet s
is_null _ = False

instance Outputable UnVarGraph where
  ppr (Del d g) = text "Del" <+> ppr (sizeUnVarSet d) <+> parens (ppr g)
  ppr (Union a b) = text "Union" <+> parens (ppr a) <+> parens (ppr b)
  ppr (CG s) = text "CG" <+> ppr (sizeUnVarSet s)
  ppr (CBPG a b) = text "CBPG" <+> ppr (sizeUnVarSet a) <+> ppr (sizeUnVarSet b)
