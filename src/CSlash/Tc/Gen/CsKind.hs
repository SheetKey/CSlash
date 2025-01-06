module CSlash.Tc.Gen.CsKind where

import CSlash.Cs
import CSlash.Rename.Utils
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.LclEnv
-- import GHC.Tc.Types.Constraint
import CSlash.Tc.Utils.Env
import CSlash.Tc.Utils.TcMType
-- import GHC.Tc.Validity
-- import GHC.Tc.Utils.Unify
-- import GHC.IfaceToCore
import CSlash.Tc.Solver
-- import GHC.Tc.Zonk.Type
import CSlash.Tc.Utils.TcType
-- import GHC.Tc.Utils.Instantiate ( tcInstInvisibleTyBinders, tcInstInvisibleTyBindersN,
--                                   tcInstInvisibleTyBinder, tcSkolemiseInvisibleBndrs,
--                                   tcInstTypeBndrs )
import CSlash.Tc.Zonk.TcType

import CSlash.Core.Type
import CSlash.Core.Type.Rep
import CSlash.Core.Type.Ppr
import CSlash.Core.Kind

import CSlash.Builtin.Types.Prim
import CSlash.Types.Error
import CSlash.Types.Name.Env
import CSlash.Types.Name.Reader( lookupLocalRdrOcc )
import CSlash.Types.Var
import CSlash.Types.Var.Set
import CSlash.Core.TyCon
import CSlash.Core.ConLike
import CSlash.Core.DataCon
-- import CSlash.Core.Class
import CSlash.Types.Name
import CSlash.Types.Var.Env
import CSlash.Builtin.Types
import CSlash.Types.Basic
import CSlash.Types.SrcLoc
import CSlash.Types.Unique
import CSlash.Types.Unique.FM
import CSlash.Utils.Misc
import CSlash.Types.Unique.Supply
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Builtin.Names hiding ( wildCardName )
import CSlash.Driver.DynFlags

import CSlash.Data.FastString
import CSlash.Data.List.Infinite ( Infinite (..) )
import qualified CSlash.Data.List.Infinite as Inf
import CSlash.Data.List.SetOps
import CSlash.Data.Maybe
import CSlash.Data.Bag( unitBag )

import Data.Function ( on )
import Data.List.NonEmpty ( NonEmpty(..), nonEmpty )
import qualified Data.List.NonEmpty as NE
import Data.List ( mapAccumL )
import Control.Monad
import Data.Tuple( swap )

tcLCsKind :: LCsKind Rn -> TcM TcKind
tcLCsKind (L span ki) = setSrcSpanA span $ tcCsKind ki

tcCsKind :: CsKind Rn -> TcM TcKind
tcCsKind CsUKd {} = return UKd
tcCsKind CsAKd {} = return AKd
tcCsKind CsLKd {} = return LKd
tcCsKind (CsKdVar _ kv) = tcKiVar (unLoc kv)
tcCsKind (CsFunKd _ k1 k2) = tc_fun_kind k1 k2
tcCsKind (CsParKd _ ki) = tcLCsKind ki

tc_fun_kind :: LCsKind Rn -> LCsKind Rn -> TcM TcKind
tc_fun_kind k1 k2 = do
  k1' <- tcLCsKind k1 
  k2' <- tcLCsKind k2
  return $ FunKd FKF_K_K k1' k2'

tcKiVar :: Name -> TcM TcKind
tcKiVar name = do
  traceTc "lk1k" (ppr name)
  thing <- tcLookup name
  case thing of
    AKiVar _ kv -> return $ mkKiVarKi kv
    _ -> wrongThingErr WrongThingKind thing name
