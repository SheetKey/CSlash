module CSlash.Tc.Utils.Unify where

import CSlash.Core.Kind (BuiltInKi)
import CSlash.Tc.Utils.TcType (AnyKind)
import CSlash.Tc.Types.Evidence (CsWrapper)
import CSlash.Tc.Types (TcM)
import CSlash.Tc.Types.Origin (CtOrigin)

tcSubMult :: CtOrigin -> BuiltInKi -> AnyKind -> TcM CsWrapper
