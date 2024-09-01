module CSlash.Core.Unfold where

data UnfoldingOpts = UnfoldingOpts
  { unfoldingCreationTHreshold :: !Int
  , unfoldingUseThreshold :: !Int
  , unfoldingFunAppDiscount :: !Int
  , unfoldingDictDiscount :: !Int
  , unfoldingAggression :: !Bool
  , unfoldingCaseThreshold :: !Int
  , unfoldingCaseScaling :: !Int
  , unfoldingReportPrefix :: !(Maybe String)
  }
