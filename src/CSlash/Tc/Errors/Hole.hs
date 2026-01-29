module CSlash.Tc.Errors.Hole where

import CSlash.Tc.Errors.Types ( HoleFitDispConfig(..) )
import CSlash.Tc.Types
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Origin
import CSlash.Tc.Utils.TcMType
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Zonk.TcType
import CSlash.Core.Type
import CSlash.Core.TyCon( TyCon )
import CSlash.Core.Type.Rep( Type(..) )
import CSlash.Core.DataCon
import CSlash.Core.Predicate( KiPred(..), classifyPredKind )
import CSlash.Types.Name
import CSlash.Types.Name.Reader
-- import CSlash.Builtin.Names ( gHC_INTERNAL_ERR, gHC_INTERNAL_UNSAFE_COERCE )
import CSlash.Types.Var.Id
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Types.TyThing
import CSlash.Data.Bag
import CSlash.Core.ConLike ( ConLike(..) )
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Tc.Utils.Env (tcLookup)
import CSlash.Utils.Outputable
import CSlash.Driver.DynFlags
import CSlash.Data.Maybe
import CSlash.Utils.FV ( unionFV, mkFVs, FV )

import Control.Arrow ( (&&&) )

import Control.Monad    ( filterM, replicateM, foldM )
import Data.List        ( partition, sort, sortOn, nubBy )
import Data.Graph       ( graphFromEdges, topSort )

import CSlash.Tc.Solver    ( simplifyTopWanteds )
-- import GHC.Tc.Solver.Monad ( runTcSEarlyAbort )
-- import GHC.Tc.Utils.Unify ( tcSubTypeSigma )

-- import GHC.HsToCore.Docs ( extractDocs )
-- import GHC.Hs.Doc
import CSlash.Unit.Module.ModIface ( ModIface_(..) )
import CSlash.Iface.Load  ( loadInterfaceForName )

import CSlash.Builtin.Utils (knownKeyNames)

-- import CSlash.Tc.Errors.Hole.FitTypes
import qualified Data.Set as Set
import CSlash.Types.SrcLoc
import CSlash.Data.FastString (NonDetFastString(..))
import CSlash.Types.Unique.Map

getHoleFitDispConfig :: TcM HoleFitDispConfig
getHoleFitDispConfig = return HFDC  
