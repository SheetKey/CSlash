module CSlash.Tc.Instance.Relation where

import CSlash.Driver.DynFlags

import CSlash.Core.Type.Rep

import CSlash.Tc.Utils.Env
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Utils.TcType
-- import GHC.Tc.Utils.Instantiate(instDFunType, tcInstType)
-- import GHC.Tc.Instance.Typeable
import CSlash.Tc.Utils.TcMType
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Types.Origin (InstanceWhat (..))
-- import GHC.Tc.Instance.Family( tcGetFamInstEnvs, tcInstNewTyCon_maybe, tcLookupDataFamInst )
import CSlash.Rename.Env( addUsedGRE )

import CSlash.Builtin.Types
import CSlash.Builtin.Types.Prim
import CSlash.Builtin.Names
-- import GHC.Builtin.PrimOps ( PrimOp(..) )
-- import GHC.Builtin.PrimOps.Ids ( primOpId )

import CSlash.Types.Name.Reader
import CSlash.Types.Name   ( Name )
import CSlash.Types.Var.Env ( VarEnv )
import CSlash.Types.Id
import CSlash.Types.Var

import CSlash.Core.Predicate
import CSlash.Core.Kind
import CSlash.Core.Type
-- import GHC.Core.Make ( mkCharExpr, mkNaturalExpr, mkStringExprFS, mkCoreLams )
import CSlash.Core.DataCon
import CSlash.Core.TyCon

import CSlash.Core ( Expr(..) )

import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc( splitAtList, fstOf3 )
import CSlash.Data.FastString

import CSlash.Unit.Module.Warnings

import CSlash.Cs.Extension

import CSlash.Types.Id.Info
import CSlash.Tc.Errors.Types
import Control.Monad

import Data.Functor
import Data.Maybe

{- *******************************************************************
*                                                                    *
                       Inst lookup
*                                                                    *
******************************************************************* -}

data RelInstResult
  = NoInstance
  | OneInst { rir_canonical :: Bool
            , rir_what :: InstanceWhat
            }
  | NotSure

instance Outputable RelInstResult where
  ppr NoInstance = text "NoInstance"
  ppr NotSure = text "NotSure"
  ppr (OneInst _ what) = text "OneInst" <+> ppr what

instanceShouldBeSaved :: InstanceWhat -> Bool
instanceShouldBeSaved BuiltinEqInstance = False
instanceShouldBeSaved BuiltinInstance = True
instanceShouldBeSaved LocalInstance = False

matchGlobalInst :: DynFlags -> Bool -> KiCon -> MonoKind -> MonoKind -> TcM RelInstResult
matchGlobalInst dflags short_cut kc k1 k2 = case kc of
  LTKi -> matchLTEQKi False k1 k2
  LTEQKi -> matchLTEQKi True k1 k2
  EQKi -> pprPanic "matchGlobalInst/EQKi" (ppr k1 $$ ppr k2)
  other -> pprPanic "matchGlobalInst/other" (ppr other $$ ppr k1 $$ ppr k2)

matchLTEQKi :: Bool -> MonoKind -> MonoKind -> TcM RelInstResult
matchLTEQKi eq_ok (KiConApp kc1 []) (KiConApp kc2 [])
  = if (kc1 == kc2 && eq_ok) || kc1 < kc2
    then return $ OneInst True BuiltinInstance
    else return $ NoInstance
matchLTEQKi True (KiVarKi v1) (KiVarKi v2)
  | v1 == v2
  = return $ OneInst True BuiltinInstance
matchLTEQKi _ _ _ = return $ NotSure
