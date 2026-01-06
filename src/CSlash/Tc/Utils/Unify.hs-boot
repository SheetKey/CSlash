module CSlash.Tc.Utils.Unify where

import CSlash.Core.Kind (BuiltInKi, KiPredCon)
import CSlash.Tc.Utils.TcType (AnyTauType, AnyKind, AnyMonoKind, AnyTypeCoercion, AnyKindCoercion)
import CSlash.Tc.Types.Evidence (AnyCsWrapper)
import CSlash.Tc.Types (TcM)
import CSlash.Tc.Types.Origin (CtOrigin, KindedThing)

tcSubMult :: CtOrigin -> BuiltInKi -> AnyKind -> TcM AnyCsWrapper

unifyInvisibleType :: AnyTauType -> AnyTauType -> TcM AnyTypeCoercion

unifyKind :: Maybe KindedThing -> KiPredCon -> AnyMonoKind -> AnyMonoKind -> TcM AnyKindCoercion
