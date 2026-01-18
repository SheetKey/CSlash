module CSlash.CsToCore.Types where

import Data.IORef
import qualified Data.Set as S

-- import GHC.Types.CostCentre.State
import CSlash.Types.Error
import CSlash.Types.Name.Env
import CSlash.Types.SrcLoc
import CSlash.Types.Var
import CSlash.Types.Name.Reader (GlobalRdrEnv)
import CSlash.Cs (CsExpr, Zk)
import CSlash.Tc.Types (TcRnIf, IfGblEnv, IfLclEnv)
-- import GHC.HsToCore.Pmc.Types (Nablas)
import CSlash.CsToCore.Errors.Types
import CSlash.Core (CoreExpr)
import CSlash.Utils.Outputable as Outputable
import CSlash.Unit.Module
-- import GHC.Driver.Hooks (DsForeignsHook)
import CSlash.Data.OrdList (OrdList)
-- import GHC.Types.ForeignStubs (ForeignStubs)
import CSlash.Types.CompleteMatch

{- *********************************************************************
*                                                                      *
                Desugarer monad
*                                                                      *
********************************************************************* -}

data DsGblEnv = DsGblEnv
  { ds_mod :: Module
  , ds_gbl_rdr_env :: GlobalRdrEnv
  , ds_name_ppr_ctx :: NamePprCtx
  , ds_msgs :: IORef (Messages DsMessage)
  , ds_if_env :: (IfGblEnv, IfLclEnv)
  , ds_complete_matches :: DsCompleteMatches
  }

instance ContainsModule DsGblEnv where
  extractModule = ds_mod

data DsLclEnv = DsLclEnv
  { dsl_loc :: RealSrcSpan
  }

type DsM = TcRnIf DsGblEnv DsLclEnv
