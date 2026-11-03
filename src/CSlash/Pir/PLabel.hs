{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module CSlash.Pir.PLabel where

import Prelude hiding ((<>))

import CSlash.Types.Var.Id.Info
import CSlash.Types.Basic
-- import {-# SOURCE #-} CSlash.Pir.BlockId (BlockId, mkBlockId)
import CSlash.Unit.Types
import CSlash.Types.Name
import CSlash.Types.Unique
import CSlash.Builtin.PrimOps
-- import GHC.Types.CostCentre
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Trace
import CSlash.Data.FastString
import CSlash.Platform
import CSlash.Types.Unique.Set
import CSlash.Core.Ppr ( {- instances -} )
import CSlash.Types.SrcLoc

import qualified Data.Semigroup as S

data PLabel
  = IdLabel Name CafInfo IdLabelInfo

pprPLabel :: forall doc. IsLine doc => Platform -> PLabel -> doc 
{-# SPECIALIZE pprPLabel :: Platform -> PLabel -> SDoc #-}
{-# SPECIALIZE pprPLabel :: Platform -> PLabel -> HLine #-}
pprPLabel @doc !platform lbl =
  let tempLabelPrefixOrUnderscore :: doc
      tempLabelPrefixOrUnderscore = char '_'
  in case lbl of
       IdLabel name _ flavor -> pprName name <> ppIdFlavor flavor

instance OutputableP Platform PLabel where
  {-# INLINE pdoc #-}
  pdoc !platform lbl = getPprStyle $ \pp_sty ->
    case pp_sty of
      PprDump{} -> pprPLabel platform lbl
      _ -> let lbl_doc = pprPLabel platform lbl
           in pprTraceUserWarning (text "Labels in code should be printed with pprCLabel" <> lbl_doc) lbl_doc

ppIdFlavor :: IsLine doc => IdLabelInfo -> doc
ppIdFlavor x = pp_pSEP <> case x of
  Function -> text "function"
  Entry -> text "entry"

pp_pSEP :: IsLine doc => doc
pp_pSEP = char '_'

data IdLabelInfo
  = Function
  | Entry

-- -----------------------------------------------------------------------------
-- Constructing PLabels
-- -----------------------------------------------------------------------------

mkFunctionLabel :: Name -> CafInfo -> PLabel
mkFunctionLabel name c = IdLabel name c Function

mkEntryLabel :: Name -> CafInfo -> PLabel
mkEntryLabel name c = IdLabel name c Entry

-- -----------------------------------------------------------------------------
-- Convert between different kinds of label

toEntryLbl :: Platform -> PLabel -> PLabel
toEntryLbl platform lbl = case lbl of
  IdLabel n c Function -> IdLabel n c Entry
  IdLabel n c Entry -> IdLabel n c Entry

toProcDelimiterLbl :: PLabel -> PLabel
toProcDelimiterLbl lbl = case lbl of
  -- LocalBlockLabel{}
  _ -> lbl
