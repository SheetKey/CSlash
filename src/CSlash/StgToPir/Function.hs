{-# LANGUAGE MultiParamTypeClasses #-}

module CSlash.StgToPir.Function
  ( module CSlash.StgToPir.Function
  , LambdaFormInfo
  ) where

import CSlash.Cs.Pass
import CSlash.Platform
import CSlash.Platform.Profile

import CSlash.Stg.Syntax
-- import GHC.Runtime.Heap.Layout
import CSlash.Pir
-- import CSlash.Pir.Utils
import CSlash.StgToPir.Types
-- import GHC.StgToCmm.Sequel

-- import GHC.Types.CostCentre
import CSlash.Pir.BlockId
import CSlash.Pir.PLabel
import CSlash.Types.Var.Id
import CSlash.Types.Var.Class
import CSlash.Types.Var.Id.Info
import CSlash.Core.DataCon
import CSlash.Types.Name hiding (varName)
import CSlash.Core.Type
import CSlash.Core.Type.Rep
import CSlash.Tc.Utils.TcType
import CSlash.Core.TyCon
import CSlash.Types.RepType
import CSlash.Types.Basic
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Data.Maybe (isNothing)

import Data.Coerce (coerce)
import qualified Data.ByteString.Char8 as BS8
import CSlash.StgToPir.Config
-- import GHC.Stg.InferTags.TagSig (isTaggedSig)

-----------------------------------------------------------------------------
--                Data types and synonyms
-----------------------------------------------------------------------------

data CgLoc
  = PirLoc PirExpr
  | LneLoc BlockId [LocalReg]

instance OutputableP Platform CgLoc where
  pdoc = pprCgLoc

pprCgLoc :: Platform -> CgLoc -> SDoc
pprCgLoc platform (PirLoc e) = text "pir" <+> pdoc platform e
pprCgLoc _ (LneLoc b rs) = text "lne" <+> ppr b <+> ppr rs

-------------------------------------
--        Non-void types
-------------------------------------

newtype NonVoid a = NonVoid a
  deriving (Eq, Show)

fromNonVoid :: NonVoid a -> a
fromNonVoid (NonVoid a) = a

instance (Outputable a) => Outputable (NonVoid a) where
  ppr (NonVoid a) = ppr a

nonVoidIds :: [Id Zk] -> [NonVoid (Id Zk)]
nonVoidIds ids = [NonVoid id | id <- ids, not (isZeroBitTy (varType id))]

-----------------------------------------------------------------------------
--              Data types for function information
-----------------------------------------------------------------------------

data FunctionInfo = FunctionInfo
  { functionName :: !(Id Zk)
  , functionLFInfo :: !LambdaFormInfo
  , functionLabel :: !PLabel
  , functionProf :: !ProfilingInfo
  }

--------------------------------------
--        Building FunctionInfos
--------------------------------------

mkFunctionInfo
  :: Profile
  -> Id Zk
  -> LambdaFormInfo
  -> String
  -> FunctionInfo
mkFunctionInfo profile id lf_info val_descr
  = FunctionInfo { functionName = id
                 , functionLFInfo = lf_info
                 , functionLabel = lbl
                 , functionProf = prof }
  where
    prof = mkProfilingInfo profile id val_descr
    lbl = mkFunctionLabel (varName id) (idCafInfo id)

--------------------------------------
--   Profiling
--------------------------------------

mkProfilingInfo :: Profile -> Id Zk -> String -> ProfilingInfo
mkProfilingInfo profile id val_descr
  | not (profileIsProfiling profile) = NoProfilingInfo
  | otherwise = panic "profiling"
