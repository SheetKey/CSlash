module CSlash.Types.TypeEnv where

-- import GHC.Core.Class
-- import GHC.Core.Coercion.Axiom
import CSlash.Core.ConLike
import CSlash.Core.DataCon
-- import GHC.Core.FamInstEnv
-- import GHC.Core.PatSyn
import CSlash.Core.TyCon

import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Var
import CSlash.Types.TyThing

type TypeEnv = NameEnv TyThing