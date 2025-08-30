module CSlash.Tc.Utils.TcMType where

import CSlash.Tc.Types
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Utils.TcType
import CSlash.Types.Name

tcCheckUsage :: Name -> AnyKind -> TcM a -> TcM (a, CsWrapper)
