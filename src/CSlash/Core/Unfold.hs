module CSlash.Core.Unfold where

data UnfoldingOpts = UnfoldingOpts
  { unfoldingCreationThreshold :: !Int
  , unfoldingUseThreshold :: !Int
  , unfoldingFunAppDiscount :: !Int
  , unfoldingDictDiscount :: !Int
  , unfoldingAggression :: !Bool
  , unfoldingCaseThreshold :: !Int
  , unfoldingCaseScaling :: !Int
  , unfoldingReportPrefix :: !(Maybe String)
  }

defaultUnfoldingOpts :: UnfoldingOpts
defaultUnfoldingOpts = UnfoldingOpts
  { unfoldingCreationThreshold = 750
  , unfoldingUseThreshold = 90
  , unfoldingFunAppDiscount = 60
  , unfoldingDictDiscount = 30
  , unfoldingAggression = False
  , unfoldingCaseThreshold = 2
  , unfoldingCaseScaling = 30
  , unfoldingReportPrefix = Nothing
  }
