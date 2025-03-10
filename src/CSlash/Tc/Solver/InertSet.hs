module CSlash.Tc.Solver.InertSet where

import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Origin
-- import CSlash.Tc.Solver.Types
import CSlash.Tc.Utils.TcType

import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Basic( SwapFlag(..) )

-- import GHC.Core.Reduction
-- import GHC.Core.Predicate
import CSlash.Core.Type.FVs
import qualified CSlash.Core.Type.Rep as Rep
-- import GHC.Core.Class( Class )
import CSlash.Core.TyCon
-- import GHC.Core.Class( classTyCon )
-- import GHC.Core.Unify

import CSlash.Utils.Misc ( partitionWith )
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Data.Maybe
import CSlash.Data.Bag

import Data.List.NonEmpty ( NonEmpty(..), (<|) )
import qualified Data.List.NonEmpty as NE
import Data.Function ( on )

import Control.Monad ( forM_ )

{- *********************************************************************
*                                                                      *
                  Worklists
*                                                                      *
********************************************************************* -}

data WorkList = WL
  { wl_eqs :: [Ct]
  , wl_rest :: [Ct]
  , wl_implics :: Bag Implication
  }

extendWorkListEq :: Ct -> WorkList -> WorkList
extendWorkListEq ct wl = wl { wl_eqs = ct : wl_eqs wl }

extendWorkListEqs :: Bag Ct -> WorkList -> WorkList
extendWorkListEqs eqs wl = wl { wl_eqs = foldr (:) (wl_eqs wl) eqs }

extendWorkListCt :: Ct -> WorkList -> WorkList
extendWorkListCt ct wl = case ctEvPred (ctEvidence ct) of
  KiEqPred {} -> extendWorkListEq ct wl

extendWorkListCts :: Cts -> WorkList -> WorkList
extendWorkListCts cts wl = foldr extendWorkListCt wl cts

emptyWorkList :: WorkList
emptyWorkList = WL { wl_eqs = [], wl_rest = [], wl_implics = emptyBag }

{- *********************************************************************
*                                                                      *
                  InertSet
*                                                                      *
********************************************************************* -}

type CycleBreakerVarStack = NonEmpty (Bag (TcTyVar, TcType))

data InertSet = IS
  { inert_cans :: InertCans
  , inert_cycle_breakers :: CycleBreakerVarStack
  }

emptyInertCans :: InertCans
emptyInertCans = IC { inert_given_eq_lvl = topTcLevel
                    , inert_given_eqs = False
                    }

emptyInert :: InertSet
emptyInert = IS { inert_cans = emptyInertCans
                , inert_cycle_breakers = emptyBag :| []
                }

{- *********************************************************************
*                                                                      *
                InertCans: the canonical inerts
*                                                                      *
********************************************************************* -}

data InertCans = IC
  { inert_given_eq_lvl :: TcLevel
  , inert_given_eqs :: Bool
  }

instance Outputable InertCans where
  ppr (IC { inert_given_eq_lvl = ge_lvl
          , inert_given_eqs = given_eqs })
    = braces $ vcat
      [ text "Innermost given equalities =" <+> ppr ge_lvl
      , text "Given eqs at this level =" <+> ppr given_eqs
      ]

{- *********************************************************************
*                                                                      *
    Adding to and removing from the inert set
*                                                                      *
********************************************************************* -}

data KickOutSpec
  = KOAfterUnify VarSet

kickOutRewritableLHS :: KickOutSpec -> CtFlavor -> InertCans -> (Cts, InertCans)
kickOutRewritableLHS _ _ ics@(IC _ _) = (emptyBag, ics)

{- *********************************************************************
*                                                                      *
    Cycle breakers
*                                                                      *
********************************************************************* -}

forAllCycleBreakerBindings_
  :: Monad m => CycleBreakerVarStack -> (TcTyVar -> TcType -> m ()) -> m ()
forAllCycleBreakerBindings_ (top_env :| _) action
  = forM_ top_env (uncurry action)
{-# INLINABLE forAllCycleBreakerBindings_ #-}
