module CSlash.Tc.Types.LclEnv where

import CSlash.Tc.Utils.TcType ( TcLevel )
-- import GHC.Tc.Errors.Types ( TcRnMessage )

-- import GHC.Core.UsageEnv ( UsageEnv )

import CSlash.Types.Name.Reader ( LocalRdrEnv )
import CSlash.Types.Name.Env ( NameEnv )
import CSlash.Types.SrcLoc ( RealSrcSpan )
import CSlash.Types.Basic ( TopLevelFlag )

import CSlash.Types.Error ( Messages )

-- import CSlash.Tc.Types.BasicTypes
-- import GHC.Tc.Types.TH
-- import GHC.Tc.Types.TcRef
-- import GHC.Tc.Types.ErrCtxt
-- import GHC.Tc.Types.Constraint ( WantedConstraints )

{- *********************************************************************
*                                                                      *
                The local typechecker environment
*                                                                      *
********************************************************************* -}

data TcLclEnv = TcLclEnv
  -- { tcl_lcl_ctxt :: !TcLclCtxt
  -- , tcl_usage :: TcRef UsageEnv
  -- , tcl_lie :: TcRef WantedConstraints
  -- , tcl_errs :: TcRef (Messages TcRnMessage)
  -- }
