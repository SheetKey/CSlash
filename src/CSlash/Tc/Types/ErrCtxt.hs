module CSlash.Tc.Types.ErrCtxt where

import CSlash.Types.Var.Env
import CSlash.Tc.Zonk.Monad (ZonkM)
import CSlash.Utils.Outputable

type ErrCtxt = (Bool, TidyEnv -> ZonkM (TidyEnv, SDoc))
