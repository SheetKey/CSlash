module CSlash.Tc.Types.ErrCtxt where

import CSlash.Types.Var.Env
import CSlash.Tc.Zonk.Monad (ZonkM)
import CSlash.Utils.Outputable
import CSlash.Types.Var (AnyTyVar, AnyKiVar)

type ErrCtxt = ( Bool
               , MkTidyEnv (AnyTyVar AnyKiVar) AnyKiVar
                 -> ZonkM (MkTidyEnv (AnyTyVar AnyKiVar) AnyKiVar, SDoc))
