module CSlash.Core.UsageEnv where

import Data.Foldable

import CSlash.Core.Kind
import CSlash.Types.Var
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

data Usage = Zero | Bottom | MUsage

data UsageEnv = UsageEnv !(NameEnv Mult) Bool

zeroUE :: UsageEnv
zeroUE = UsageEnv emptyNameEnv False

bottomUE :: UsageEnv
bottomUE = UsageEnv emptyNameEnv True

addUE :: UsageEnv -> UsageEnv -> UsageEnv
addUE (UsageEnv e1 b1) (UsageEnv e2 b2)
  = UsageEnv (plusNameEnv_C mkMultAdd e1 e2) (b1 || b2)

scaleUE :: Mult -> UsageEnv -> UsageEnv
scaleUE m (UsageEnv e _) = UsageEnv (mapNameEnv (mkMultMul m) e) False

supUE :: UsageEnv -> UsageEnv -> UsageEnv
supUE (UsageEnv e1 False) (UsageEnv e2 False)
  = UsageEnv (plusNameEnv_CD mkMultSup e1 UKd e1 UKd) False
supUE (UsageEnv e1 b1) (UsageEnv e2 b2) = UsageEnv (plusNameEnv_CD2 combineUsage e1 e2) (b1 && b2)
  where
    combineUsage (Just x) (Just y) = mkMultSup x y
    combineUsage Nothing (Just x) | b1 = x
                                  | otherwise = UKd
    combineUsage (Just x) Nothing | b2 = x
                                  | otherwise = UKd
    combineUsage Nothing Nothing = pprPanic "supUE" (ppr e1 <+> ppr e2)

supUEs :: [UsageEnv] -> UsageEnv
supUEs = foldr supUE bottomUE

instance Outputable UsageEnv where
  ppr (UsageEnv ne b) = text "UsageEnv:" <+> ppr ne <+> ppr b
