module CSlash.Tc.Types.ErrCtxt where

import CSlash.Cs.Pass

import CSlash.Types.Var.Env
import CSlash.Tc.Zonk.Monad (ZonkM)
import CSlash.Utils.Outputable

type ErrCtxt = ( Bool
               , TidyEnv Tc
                 -> ZonkM (TidyEnv Tc, SDoc))
