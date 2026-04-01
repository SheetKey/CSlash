module CSlash.Core.Opt.Simplify.Env where

import CSlash.Core.Opt.Coercion ( OptCoercionOpts )
-- import CSlash.Core.Opt.Arity ( ArityOpts(..) )
-- import GHC.Core.Opt.Simplify.Monad
import CSlash.Core
import CSlash.Core.Utils
import CSlash.Core.Unfold
-- import CSlash.Core.Subst (emptyIdSubstEnv)
import CSlash.Core.Kind
-- import CSlash.Core.Make            ( mkWildValBinder, mkCoreLet )
import CSlash.Core.Type hiding     ( substTy, substTyVar, substTyVarBndr, substCo
                                   , extendTvSubst, extendCvSubst )
-- import qualified GHC.Core.Coercion as Coercion
-- import GHC.Core.Coercion hiding ( substCo, substCoVar, substCoVarBndr )
import qualified CSlash.Core.Type as Type

import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Var.Id as Id
import CSlash.Types.Basic
import CSlash.Types.Unique.FM      ( pprUniqFM )

import CSlash.Data.OrdList
import CSlash.Data.Graph.UnVar

import CSlash.Builtin.Types
import CSlash.Platform ( Platform )

import CSlash.Utils.Monad
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc

import Data.List ( intersperse, mapAccumL )

data SimplMode = SimplMode

instance Outputable SimplMode

data FloatEnable
