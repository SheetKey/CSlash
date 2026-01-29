module CSlash.Tc.Utils.TcMType where

import CSlash.Cs.Pass

import CSlash.Core.Kind
import CSlash.Tc.Types
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Utils.TcType
import CSlash.Types.Name

tcCheckUsage :: Name -> Kind Tc -> TcM a -> TcM (a, CsWrapper Tc)
