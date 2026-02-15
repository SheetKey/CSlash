module CSlash.CsToCore.Utils where

import CSlash.Cs
import CSlash.Core
import CSlash.CsToCore.Monad

-- import CSlash.Core.Utils
-- import CSlash.Core.Make
import CSlash.Types.Var.Id.Make
import CSlash.Types.Var.Id
import CSlash.Types.Literal
import CSlash.Core.TyCon
import CSlash.Core.DataCon
import CSlash.Core.Type
import CSlash.Builtin.Types
import CSlash.Core.ConLike
import CSlash.Types.Unique.Set
import CSlash.Types.Unique.Supply
import CSlash.Unit.Module
import CSlash.Builtin.Names
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Types.SrcLoc
import CSlash.Types.Tickish
import CSlash.Utils.Misc
import CSlash.Driver.DynFlags
import CSlash.Driver.Ppr

import CSlash.Tc.Types.Evidence

import Control.Monad (zipWithM)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NEL
import Data.Maybe (maybeToList)

{-**********************************************************************
*                                                                      *
           Desugarer's version of Core Functions
*                                                                      *
**********************************************************************-}

mkCastDs :: CoreExpr -> TypeCoercion Zk -> CoreExpr
mkCastDs e co | isReflTyCo co = e
              | otherwise = Cast e co

{- *********************************************************************
*                                                                      *
              Ticks
*                                                                      *
********************************************************************* -}

mkOptTickBox :: [CoreTickish] -> CoreExpr -> CoreExpr
mkOptTickBox = flip (foldr Tick)
