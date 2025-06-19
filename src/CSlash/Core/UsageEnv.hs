module CSlash.Core.UsageEnv where

import Data.Foldable

import CSlash.Core.Kind
import CSlash.Types.Var
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

data Usage = Zero | Bottom | MUsage

data UsageEnv = UsageEnv !(NameEnv (Kind KiVar)) Bool

zeroUE :: UsageEnv
zeroUE = UsageEnv emptyNameEnv False
