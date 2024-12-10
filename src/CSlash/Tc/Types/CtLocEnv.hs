module CSlash.Tc.Types.CtLocEnv where

import CSlash.Types.SrcLoc
import CSlash.Types.Name.Reader

import CSlash.Tc.Types.BasicTypes
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Types.ErrCtxt

data CtLocEnv = CtLocEnv
  { ctl_ctxt :: ![ErrCtxt]
  , ctl_loc :: !RealSrcSpan
  , ctl_bndrs :: !TcBinderStack
  , ctl_tclvl :: !TcLevel
  , ctl_rdr :: !LocalRdrEnv
  }
