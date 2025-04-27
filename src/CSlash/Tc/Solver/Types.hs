module CSlash.Tc.Solver.Types where

import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Origin
import CSlash.Tc.Utils.TcType

import CSlash.Types.Unique
import CSlash.Types.Unique.DFM

-- import GHC.Core.Class
-- import CSlash.Core.Map.Type
-- import GHC.Core.Predicate
import CSlash.Core.TyCon
-- import CSlash.Core.TyCon.Env

import CSlash.Data.Bag
import CSlash.Data.Maybe
-- import GHC.Data.TrieMap
import CSlash.Utils.Constants
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

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
