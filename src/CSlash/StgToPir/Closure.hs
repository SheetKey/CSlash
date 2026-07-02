{-# LANGUAGE MultiParamTypeClasses #-}

module CSlash.StgToPir.Closure
  ( module CSlash.StgToPir.Closure
  , LambdaFormInfo
  ) where

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
import CSlash.Types.Var.Id.Info
import CSlash.Core.DataCon
import CSlash.Types.Name
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
