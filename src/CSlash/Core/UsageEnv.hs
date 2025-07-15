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

addUE :: UsageEnv -> UsageEnv -> UsageEnv
addUE (UsageEnv e1 b1) (UsageEnv e2 b2)
  = UsageEnv (plusNameEnv_C mkMultAdd e1 e2) (b1 || b2)

scaleUE :: Mult -> UsageEnv -> UsageEnv
scaleUE m (UsageEnv e _) = UsageEnv (mapNameEnv (mkMultMul m) e) False

instance Outputable UsageEnv where
  ppr (UsageEnv ne b) = text "UsageEnv:" <+> ppr ne <+> ppr b
