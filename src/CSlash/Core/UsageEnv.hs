{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Core.UsageEnv where

import CSlash.Cs.Pass

import CSlash.Core.Kind
import CSlash.Types.Var
import CSlash.Types.Var.Id
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Data.Foldable

import qualified Data.Data as Data

data Usage = Zero | One | Many
  deriving Data.Data

instance Outputable Usage where
  ppr Zero = text "0"
  ppr One = text "1"
  ppr Many = text "Many"

data Scaled a = Scaled !Usage a
  deriving Data.Data

instance Outputable a => Outputable (Scaled a) where
  ppr (Scaled _ t) = ppr t

scaledThing :: Scaled a -> a
scaledThing (Scaled _ a) = a

addUsage :: Usage -> Usage -> Usage
addUsage Zero u = u
addUsage u Zero = u
addUsage _ _ = Many

supUsage :: Usage -> Usage -> Usage
supUsage Many _ = Many
supUsage _ Many = Many
supUsage One _ = One
supUsage _ One = One
supUsage _ _ = Zero

-- Takes the kind of a binder and gives the usage to scale the RHS of the binding
bindingKindUsage :: MonoKind p -> Usage
bindingKindUsage ki = case splitInvisFunKis ki of
  (_, FunKi{}) -> pprPanic "bindingKindUsage" (ppr ki)
  (_, KiPredApp{}) -> pprPanic "bindingKindUsage" (ppr ki)
  (_, BIKi UKd) -> Zero
  (_, BIKi AKd) -> Zero
  (_, BIKi LKd) -> One
  (preds, KiVarKi kv) -> panic "bindingKindUsage"

data UsageEnv = UsageEnv !(NameEnv Usage)

singleUsageUE :: Id Tc -> UsageEnv
singleUsageUE x | isExternalName n = emptyUE
                | otherwise = UsageEnv (unitNameEnv n One)
  where n = getName x

emptyUE :: UsageEnv
emptyUE = UsageEnv emptyNameEnv

addUE :: UsageEnv -> UsageEnv -> UsageEnv
addUE (UsageEnv e1) (UsageEnv e2)
  = UsageEnv (plusNameEnv_C addUsage e1 e2)

scaleUE :: Usage -> UsageEnv -> UsageEnv
scaleUE u (UsageEnv e) = UsageEnv (mapNameEnv (supUsage u) e)

supUE :: UsageEnv -> UsageEnv -> UsageEnv
supUE (UsageEnv e1) (UsageEnv e2) = UsageEnv (plusNameEnv_CD supUsage e1 Zero e2 Zero)

supUEs :: [UsageEnv] -> UsageEnv
supUEs = foldr supUE emptyUE
 
deleteUE :: NamedThing n => UsageEnv -> n -> UsageEnv
deleteUE (UsageEnv e) x = UsageEnv (delFromNameEnv e (getName x))

lookupUE :: NamedThing n => UsageEnv -> n -> Usage
lookupUE (UsageEnv e) x = case lookupNameEnv e (getName x) of
                            Just u -> u
                            Nothing -> Zero

instance Outputable UsageEnv where
  ppr (UsageEnv ne) = text "UsageEnv:" <+> ppr ne
