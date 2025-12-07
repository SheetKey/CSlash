module CSlash.Tc.Utils.Unify where

import CSlash.Core.Kind (BuiltInKi)
import CSlash.Tc.Utils.TcType (AnyTauType, AnyKind, AnyTypeCoercion)
import CSlash.Tc.Types.Evidence (AnyCsWrapper)
import CSlash.Tc.Types (TcM)
import CSlash.Tc.Types.Origin (CtOrigin)

tcSubMult :: CtOrigin -> BuiltInKi -> AnyKind -> TcM AnyCsWrapper

unifyInvisibleType :: AnyTauType -> AnyTauType -> TcM AnyTypeCoercion
