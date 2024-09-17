module CSlash.Core.Unfold where

data UnfoldingOpts = UnfoldingOpts
  { unfoldingCreationThreshold :: !Int
  , unfoldingUseThreshold :: !Int
  , unfoldingFunAppDiscount :: !Int
  , unfoldingDictDiscount :: !Int
  , unfoldingVeryAggressive :: !Bool
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
  , unfoldingVeryAggressive = False
  , unfoldingCaseThreshold = 2
  , unfoldingCaseScaling = 30
  , unfoldingReportPrefix = Nothing
  }

updateCreationThreshold :: Int -> UnfoldingOpts -> UnfoldingOpts
updateCreationThreshold n opts = opts { unfoldingCreationThreshold = n }

updateUseThreshold :: Int -> UnfoldingOpts -> UnfoldingOpts
updateUseThreshold n opts = opts { unfoldingUseThreshold = n }

updateFunAppDiscount :: Int -> UnfoldingOpts -> UnfoldingOpts
updateFunAppDiscount n opts = opts { unfoldingFunAppDiscount = n }

updateDictDiscount :: Int -> UnfoldingOpts -> UnfoldingOpts
updateDictDiscount n opts = opts { unfoldingDictDiscount = n }

updateVeryAggressive :: Bool -> UnfoldingOpts -> UnfoldingOpts
updateVeryAggressive n opts = opts { unfoldingVeryAggressive = n }

updateCaseThreshold :: Int -> UnfoldingOpts -> UnfoldingOpts
updateCaseThreshold n opts = opts { unfoldingCaseThreshold = n }

updateCaseScaling :: Int -> UnfoldingOpts -> UnfoldingOpts
updateCaseScaling n opts = opts { unfoldingCaseScaling = n }

updateReportPrefix :: Maybe String -> UnfoldingOpts -> UnfoldingOpts
updateReportPrefix n opts = opts { unfoldingReportPrefix = n }
