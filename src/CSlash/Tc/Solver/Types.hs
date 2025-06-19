{-# LANGUAGE ScopedTypeVariables #-}

module CSlash.Tc.Solver.Types where

import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Origin
import CSlash.Tc.Utils.TcType

import CSlash.Types.Unique
import CSlash.Types.Unique.DFM

-- import GHC.Core.Class
import CSlash.Core.Map.Kind
import CSlash.Core.Predicate
import CSlash.Core.TyCon
import CSlash.Core.Kind
-- import CSlash.Core.TyCon.Env

import CSlash.Data.Bag
import CSlash.Data.Maybe
import CSlash.Data.TrieMap
import CSlash.Utils.Constants
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

{- *********************************************************************
*                                                                      *
                   KcAppMap
*                                                                      *
********************************************************************* -}

type KcAppMap a = DKiConEnv (ListMap KindMap a)

isEmptyKcAppMap :: KcAppMap a -> Bool
isEmptyKcAppMap m = isEmptyDKiConEnv m

emptyKcAppMap :: KcAppMap a
emptyKcAppMap = emptyDKiConEnv

findKcApp :: KcAppMap a -> KiCon -> AnyMonoKind -> AnyMonoKind -> Maybe a
findKcApp m kc ki1 ki2 = do
  kis_map <- lookupDKiConEnv m kc
  lookupTM [ki1, ki2] kis_map

delKcApp :: KcAppMap a -> KiCon -> AnyMonoKind -> AnyMonoKind -> KcAppMap a
delKcApp m kc ki1 ki2 = adjustDKiConEnv (deleteTM [ki1, ki2]) m kc

insertKcApp :: KcAppMap a -> KiCon -> AnyMonoKind -> AnyMonoKind -> a -> KcAppMap a
insertKcApp m kc ki1 ki2 ct = alterDKiConEnv alter_km m kc
  where
    alter_km mb_km = Just (insertTM [ki1, ki2] ct (mb_km `orElse` emptyTM))

alterKcApp :: forall a. KcAppMap a -> KiCon -> AnyMonoKind -> AnyMonoKind -> XT a -> KcAppMap a
alterKcApp m kc ki1 ki2 upd = alterDKiConEnv alter_km m kc
  where
    alter_km :: Maybe (ListMap KindMap a) -> Maybe (ListMap KindMap a)
    alter_km m_elt = Just (alterTM [ki1, ki2] upd (m_elt `orElse` emptyTM))

filterKcAppMap :: forall a. (a -> Bool) -> KcAppMap a -> KcAppMap a
filterKcAppMap f m = mapMaybeDKiConEnv one_kicon m
  where
    one_kicon :: ListMap KindMap a -> Maybe (ListMap KindMap a)
    one_kicon km
      | isEmptyTM filtered_km = Nothing
      | otherwise = Just filtered_km
      where
        filtered_km = filterTM f km

kcAppMapToBag :: KcAppMap a -> Bag a
kcAppMapToBag m = foldKcAppMap consBag m emptyBag

foldKcAppMap :: (a -> b -> b) -> KcAppMap a -> b -> b
foldKcAppMap k m z = foldDKiConEnv (foldTM k) z m

{- *********************************************************************
*                                                                      *
                   RelMap
*                                                                      *
********************************************************************* -}

type RelMap a = KcAppMap a

emptyRelMap :: RelMap a
emptyRelMap = emptyKcAppMap

findRel :: RelMap a -> CtLoc -> KiCon -> AnyMonoKind -> AnyMonoKind -> Maybe a
findRel m loc kc ki1 ki2 = findKcApp m kc ki1 ki2

findRelsByRel :: RelMap a -> KiCon -> Bag a
findRelsByRel m rl = findRelsByKiConKey m (getUnique rl)

findRelsByKiConKey :: RelMap a -> Unique -> Bag a
findRelsByKiConKey m rl
  | Just km <- lookupUDFM_Directly m rl = foldTM consBag km emptyBag
  | otherwise = emptyBag

relsToBag :: RelMap a -> Bag a
relsToBag = kcAppMapToBag

foldRels :: (a -> b -> b) -> RelMap a -> b -> b
foldRels = foldKcAppMap

{- *********************************************************************
*                                                                      *
                   EqualCtList
*                                                                      *
********************************************************************* -}

type EqualCtList = [EqCt]

addToEqualCtList :: EqCt -> EqualCtList -> EqualCtList
addToEqualCtList ct old_eqs
  | debugIsOn
  = case ct of
      KiEqCt { eq_lhs = KiVarLHS kv }
        -> assert (all (shares_lhs kv) old_eqs)
           $ assertPpr (null bad_prs)
                       (vcat [ text "bad_prs" <+> ppr bad_prs
                             , text "ct:old_eqs" <+> ppr (ct : old_eqs) ])
           $ (ct : old_eqs)
  | otherwise
  = ct : old_eqs
  where
    shares_lhs kv (KiEqCt { eq_lhs = KiVarLHS old_kv }) = kv == old_kv

    bad_prs = filter is_bad_pair (distinctPairs (ct : old_eqs))
    is_bad_pair :: (EqCt, EqCt) -> Bool
    is_bad_pair (ct1, ct2) = eqCtFlavor ct1 `eqCanRewriteF` eqCtFlavor ct2

distinctPairs :: [a] -> [(a, a)]
distinctPairs [] = []
distinctPairs (x:xs) = concatMap (\y -> [(x, y), (y, x)]) xs ++ distinctPairs xs
