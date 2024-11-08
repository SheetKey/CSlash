{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module CSlash.Types.Name.Set (
  NameSet,

  emptyNameSet, unitNameSet, mkNameSet, unionNameSet, unionNameSets,
  minusNameSet, elemNameSet, extendNameSet, extendNameSetList,
  delFromNameSet, delListFromNameSet, isEmptyNameSet, filterNameSet,
  intersectsNameSet, disjointNameSet, intersectNameSet,
  nameSetAny, nameSetAll, nameSetElemsStable,

  FreeVars,

  isEmptyFVs, emptyFVs, plusFVs, plusFV,
  mkFVs, addOneFV, unitFV, delFV, delFVs,
  intersectFVs, intersectsFVs,

  Defs, Uses, DefUse, DefUses,
  emptyDUs, usesOnly, mkDUs, plusDU,
  findUses, duDefs, duUses, allUses,
  ) where

import CSlash.Types.Name
import CSlash.Data.OrdList
import CSlash.Types.Unique.Set
import Data.List (sortBy)

type NameSet = UniqSet Name

emptyNameSet       :: NameSet
unitNameSet        :: Name -> NameSet
extendNameSetList   :: NameSet -> [Name] -> NameSet
extendNameSet    :: NameSet -> Name -> NameSet
mkNameSet          :: [Name] -> NameSet
unionNameSet      :: NameSet -> NameSet -> NameSet
unionNameSets  :: [NameSet] -> NameSet
minusNameSet       :: NameSet -> NameSet -> NameSet
elemNameSet        :: Name -> NameSet -> Bool
isEmptyNameSet     :: NameSet -> Bool
delFromNameSet     :: NameSet -> Name -> NameSet
delListFromNameSet :: NameSet -> [Name] -> NameSet
filterNameSet      :: (Name -> Bool) -> NameSet -> NameSet
intersectNameSet   :: NameSet -> NameSet -> NameSet
intersectsNameSet  :: NameSet -> NameSet -> Bool
disjointNameSet    :: NameSet -> NameSet -> Bool
-- ^ True if there is a non-empty intersection.
-- @s1 `intersectsNameSet` s2@ doesn't compute @s2@ if @s1@ is empty

isEmptyNameSet    = isEmptyUniqSet
emptyNameSet      = emptyUniqSet
unitNameSet       = unitUniqSet
mkNameSet         = mkUniqSet
extendNameSetList  = addListToUniqSet
extendNameSet   = addOneToUniqSet
unionNameSet     = unionUniqSets
unionNameSets = unionManyUniqSets
minusNameSet      = minusUniqSet
elemNameSet       = elementOfUniqSet
delFromNameSet    = delOneFromUniqSet
filterNameSet     = filterUniqSet
intersectNameSet  = intersectUniqSets
disjointNameSet   = disjointUniqSets

delListFromNameSet set ns = foldl' delFromNameSet set ns

intersectsNameSet s1 s2 = not (s1 `disjointNameSet` s2)

nameSetAny :: (Name -> Bool) -> NameSet -> Bool
nameSetAny = uniqSetAny

nameSetAll :: (Name -> Bool) -> NameSet -> Bool
nameSetAll = uniqSetAll

-- | Get the elements of a NameSet with some stable ordering.
-- This only works for Names that originate in the source code or have been
-- tidied.
-- See Note [Deterministic UniqFM] to learn about nondeterminism
nameSetElemsStable :: NameSet -> [Name]
nameSetElemsStable ns =
  sortBy stableNameCmp $ nonDetEltsUniqSet ns

type FreeVars   = NameSet

plusFV   :: FreeVars -> FreeVars -> FreeVars
addOneFV :: FreeVars -> Name -> FreeVars
unitFV   :: Name -> FreeVars
emptyFVs :: FreeVars
plusFVs  :: [FreeVars] -> FreeVars
mkFVs    :: [Name] -> FreeVars
delFV    :: Name -> FreeVars -> FreeVars
delFVs   :: [Name] -> FreeVars -> FreeVars
intersectFVs :: FreeVars -> FreeVars -> FreeVars
intersectsFVs :: FreeVars -> FreeVars -> Bool

isEmptyFVs :: NameSet -> Bool
isEmptyFVs  = isEmptyNameSet
emptyFVs    = emptyNameSet
plusFVs     = unionNameSets
plusFV      = unionNameSet
mkFVs       = mkNameSet
addOneFV    = extendNameSet
unitFV      = unitNameSet
delFV n s   = delFromNameSet s n
delFVs ns s = delListFromNameSet s ns
intersectFVs = intersectNameSet
intersectsFVs = intersectsNameSet

{- *********************************************************************
*                                                                      *
                Defs and uses
*                                                                      *
********************************************************************* -}

type Defs = NameSet

type Uses = NameSet

type DefUse = (Maybe Defs, Uses)

type DefUses = OrdList DefUse

emptyDUs :: DefUses
emptyDUs = nilOL

usesOnly :: Uses -> DefUses
usesOnly uses = unitOL (Nothing, uses)

mkDUs :: [(Defs, Uses)] -> DefUses
mkDUs pairs = toOL [(Just defs, uses) | (defs, uses) <- pairs]

plusDU :: DefUses -> DefUses -> DefUses
plusDU = appOL

duDefs :: DefUses -> Defs
duDefs dus = foldr get emptyNameSet dus
  where
    get (Nothing, _u1) d2 = d2
    get (Just d1, _u1) d2 = d1 `unionNameSet` d2

allUses :: DefUses -> Uses
allUses dus = foldr get emptyNameSet dus
  where
    get (_d1, u1) u2 = u1 `unionNameSet` u2

duUses :: DefUses -> Uses
duUses dus = foldr get emptyNameSet dus
  where
    get (Nothing,   rhs_uses) uses = rhs_uses `unionNameSet` uses
    get (Just defs, rhs_uses) uses = (rhs_uses `unionNameSet` uses)
                                     `minusNameSet` defs

findUses :: DefUses -> Uses -> Uses
findUses dus uses = foldr get uses dus
  where
    get (Nothing, rhs_uses) uses
        = rhs_uses `unionNameSet` uses
    get (Just defs, rhs_uses) uses
        | defs `intersectsNameSet` uses
        || nameSetAny (startsWithUnderscore . nameOccName) defs
        = rhs_uses `unionNameSet` uses
        | otherwise
        = uses
