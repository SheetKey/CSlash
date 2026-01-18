module CSlash.CsToCore.Binds where

import CSlash.Driver.DynFlags
-- import CSlash.Driver.Config
import CSlash.Unit.Module

-- import {-# SOURCE #-}   GHC.HsToCore.Expr  ( dsLExpr )
-- import {-# SOURCE #-}   GHC.HsToCore.Match ( matchWrapper )

-- import GHC.HsToCore.Pmc.Utils( tracePm )

import CSlash.CsToCore.Monad
import CSlash.CsToCore.Errors.Types
-- import GHC.HsToCore.GuardedRHSs
-- import GHC.HsToCore.Utils
-- import GHC.HsToCore.Pmc ( addTyCs, pmcGRHSs )

import CSlash.Cs
import CSlash.Core
-- import GHC.Core.SimpleOpt    ( simpleOptExpr )
-- import GHC.Core.Opt.OccurAnal ( occurAnalyseExpr )
-- import GHC.Core.Make
-- import GHC.Core.Utils
-- import GHC.Core.Opt.Arity     ( etaExpand )
-- import GHC.Core.Unfold.Make
-- import GHC.Core.FVs
import CSlash.Core.Predicate
import CSlash.Core.TyCon
import CSlash.Core.Type
import CSlash.Core.Kind
-- import GHC.Core.Coercion
import CSlash.Core.Type.Compare( eqType )

import CSlash.Builtin.Names
-- import CSlash.Builtin.Types ( charTy )

import CSlash.Tc.Types.Evidence

import CSlash.Types.Id
-- import GHC.Types.Id.Make ( nospecId )
import CSlash.Types.Name
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Types.Var( ZkId )
import CSlash.Types.SrcLoc
import CSlash.Types.Basic
import CSlash.Types.Unique.Set( nonDetEltsUniqSet )

import CSlash.Data.Maybe
import CSlash.Data.OrdList
import CSlash.Data.Graph.Directed
import CSlash.Data.Bag
import qualified Data.Set as S

import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.Misc
import CSlash.Utils.Monad
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Control.Monad

{-**********************************************************************
*                                                                      *
           Desugaring a MonoBinds
*                                                                      *
**********************************************************************-}

dsTopLCsBinds :: LCsBinds Zk -> DsM (OrdList (ZkId, CoreExpr))
dsTopLCsBinds binds = do
  prs <- dsLCsBinds binds
  panic "dsTopLCsBinds"

dsLCsBinds :: LCsBinds Zk -> DsM [(ZkId, CoreExpr)]
dsLCsBinds binds = do
  ds_bs <- mapM dsLCsBind binds
  return $ foldr (++) [] ds_bs

dsLCsBind :: LCsBind Zk -> DsM [(ZkId, CoreExpr)]
dsLCsBind (L loc bind) = do
  dflags <- getDynFlags
  panic "putSrcSpanDs (locA loc) $ dsCsBind dflags bind"

dsCsBind :: DynFlags -> CsBind Zk -> DsM [(ZkId, CoreExpr)]
-- dsCsBind dflags b@(FunBind { fun_id = L loc fun
--                            , fun_body = body
--                            , fun_ext = (co_fn, tick)
--                            })
--   = dsCsWrapper co_fn $ \core_wrap -> do
--       body <- dsLExpr body -- might need to be special like 'tcFunBody' in the TypeChecker
--                            -- to handle the case that body is a tylam
--       let body' = mkOptTickBox tick body
--           rhs = core_wrap body'
--           core_binds = mkCorePair dflags fun False 0 rhs
--       return [core_binds]

dsCsBind _ bind = pprPanic "dsCsBind" (ppr bind)
