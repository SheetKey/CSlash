module CSlash.Core.Opt.Monad where

import CSlash.Driver.DynFlags
import CSlash.Driver.Env

-- import GHC.Core.Rules     ( RuleBase, RuleEnv, mkRuleEnv )
-- import GHC.Core.Opt.Stats ( SimplCount, zeroSimplCount, plusSimplCount )

-- import GHC.Types.Annotations
import CSlash.Types.Unique.Supply
import CSlash.Types.Name.Env
import CSlash.Types.SrcLoc
import CSlash.Types.Error

import CSlash.Utils.Error ( errorDiagnostic )
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Logger
import CSlash.Utils.Monad

import CSlash.Data.IOEnv hiding     ( liftIO, failM, failWithM )
import qualified CSlash.Data.IOEnv  as IOEnv

import CSlash.Unit.Module
import CSlash.Unit.Module.ModGuts
import CSlash.Unit.External

import Data.Bifunctor ( bimap )
import Data.Dynamic
import Data.Maybe (listToMaybe)
import Data.Word
import Control.Monad
import Control.Applicative ( Alternative(..) )

data FloatOutSwitches = FloatOutSwitches
  { floatOutAllLambdas :: Bool
  , floatOutConstants :: Bool
  , floatOutOverSatApps :: Bool
  , floatToTopLevelOnly :: Bool
  , floatJoinsToTop :: Bool
  }

instance Outputable FloatOutSwitches where
  ppr = pprFloatOutSwitches

pprFloatOutSwitches :: FloatOutSwitches -> SDoc
pprFloatOutSwitches sw
  = text "FOD" <+> (braces $
                    sep $ punctuate comma $
                    [ text "Lam =" <+> ppr (floatOutAllLambdas sw)
                    , text "Consts =" <+> ppr (floatOutConstants sw)
                    , text "JoinsToTop =" <+> ppr (floatJoinsToTop sw)
                    , text "OverSatApps =" <+> ppr (floatOutOverSatApps sw) ])
