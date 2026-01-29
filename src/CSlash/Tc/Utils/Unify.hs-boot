module CSlash.Tc.Utils.Unify where

import CSlash.Cs.Pass

import CSlash.Core.Type.Rep (TypeCoercion)
import CSlash.Core.Kind (BuiltInKi, KiPredCon, Kind, MonoKind, KindCoercion)
import CSlash.Tc.Utils.TcType (TauType)
import CSlash.Tc.Types.Evidence (CsWrapper)
import CSlash.Tc.Types (TcM)
import CSlash.Tc.Types.Origin (CtOrigin, KindedThing)

tcSubMult :: CtOrigin -> BuiltInKi -> Kind Tc -> TcM (CsWrapper Tc)

unifyInvisibleType :: TauType Tc -> TauType Tc -> TcM (TypeCoercion Tc)

unifyKind :: Maybe KindedThing -> KiPredCon -> MonoKind Tc -> MonoKind Tc -> TcM (KindCoercion Tc)
