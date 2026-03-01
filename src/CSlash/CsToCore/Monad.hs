module CSlash.CsToCore.Monad
  ( DsM
  , module CSlash.CsToCore.Monad
  ) where

import CSlash.Driver.Env
import CSlash.Driver.DynFlags
import CSlash.Driver.Ppr
import CSlash.Driver.Config.Diagnostic

import CSlash.Cs

import CSlash.CsToCore.Types
import CSlash.CsToCore.Errors.Types
-- import GHC.HsToCore.Pmc.Solver.Types (Nablas, initNablas)

import CSlash.Core
-- import GHC.Core.Make  ( unitExpr )
-- import GHC.Core.Utils ( exprType )
import CSlash.Core.DataCon
import CSlash.Core.ConLike
import CSlash.Core.TyCon
import CSlash.Core.Type
import CSlash.Core.Kind

import CSlash.IfaceToCore

import CSlash.Tc.Utils.Monad

import CSlash.Builtin.Names

import CSlash.Data.FastString

import CSlash.Unit.Env
import CSlash.Unit.External
import CSlash.Unit.Module
import CSlash.Unit.Module.ModGuts

import CSlash.Types.Name.Reader
import CSlash.Types.SourceFile
import CSlash.Types.Var.Id
-- import CSlash.Types.Var (EvId)
import CSlash.Types.SrcLoc
import CSlash.Types.TypeEnv
import CSlash.Types.Unique.Supply
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Name.Ppr
-- import CSlash.Types.Literal ( mkLitString )
-- import GHC.Types.CostCentre.State
import CSlash.Types.TyThing
import CSlash.Types.Error
import CSlash.Types.CompleteMatch
import CSlash.Types.Unique.DSet

import CSlash.Tc.Utils.Env (lookupGlobal)

import CSlash.Utils.Error
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import qualified CSlash.Data.Strict as Strict

import Data.IORef
import CSlash.Driver.Env.KnotVars
import qualified Data.Set as S
import GHC.IO.Unsafe (unsafeInterleaveIO)

{- *********************************************************************
*                                                                      *
                Data types for the desugarer
*                                                                      *
********************************************************************* -}

initDs :: CsEnv -> TcGblEnv Zk -> DsM a -> IO (Messages DsMessage, Maybe a)
initDs cs_env tcg_env thing_inside = do
  msg_var <- newIORef emptyMessages
  envs <- mkDsEnvsFromTcGbl cs_env msg_var tcg_env
  runDs cs_env envs thing_inside

mkDsEnvsFromTcGbl
  :: MonadIO m
  => CsEnv -> IORef (Messages DsMessage) -> TcGblEnv Zk -> m (DsGblEnv, DsLclEnv)
mkDsEnvsFromTcGbl cs_env msg_var tcg_env = do
  eps <- liftIO $ csEPS cs_env
  let unit_env = cs_unit_env cs_env
      this_mod = tcg_mod tcg_env
      rdr_env = tcg_rdr_env tcg_env
      type_env = tcg_type_env tcg_env
      tcg_comp_env = panic "tcg_complete_match_env tcg_env"

  ds_complete_matches <- liftIO $ unsafeInterleaveIO $
    traverse (lookupCompleteMatch type_env cs_env) =<<
    localAndImportedCompleteMatches tcg_comp_env eps

  return $ mkDsEnvs unit_env this_mod rdr_env type_env msg_var ds_complete_matches

lookupCompleteMatch :: TypeEnv -> CsEnv -> CompleteMatch -> IO DsCompleteMatch
lookupCompleteMatch type_env cs_env (CompleteMatch { cmConLikes = nms, cmResultTyCon = mb_tc })
  = do cons <- mapMUniqDSet lookup_conLike nms
       return $ CompleteMatch { cmConLikes = cons, cmResultTyCon = mb_tc }
  where
    lookup_conLike :: Name -> IO (ConLike Zk)
    lookup_conLike nm
      | Just ty <- wiredInNameTyThing_maybe nm
      = go ty
      | Just ty <- lookupTypeEnv type_env nm
      = go ty
      | otherwise
      = go =<< lookupGlobal cs_env nm
      where
        go :: TyThing Zk -> IO (ConLike Zk)
        go (AConLike cl) = return cl
        go ty = pprPanic "lookup_conLike not a ConLike" (ppr nm <+> ppr ty)

runDs :: CsEnv -> (DsGblEnv, DsLclEnv) -> DsM a -> IO (Messages DsMessage, Maybe a)
runDs cs_env (ds_gbl, ds_lcl) thing_inside = do
  res <- initTcRnIf 'd' cs_env ds_gbl ds_lcl (tryM thing_inside)
  msgs <- readIORef (ds_msgs ds_gbl)
  let final_res | errorsFound msgs = Nothing
                | Right r <- res = Just r
                | otherwise = panic "initDs"
  return (msgs, final_res)  

mkDsEnvs
  :: UnitEnv
  -> Module
  -> GlobalRdrEnv
  -> TypeEnv
  -> IORef (Messages DsMessage)
  -> DsCompleteMatches
  -> (DsGblEnv, DsLclEnv)
mkDsEnvs unit_env mod rdr_env type_env msg_var complete_matches
  = let if_genv = IfGblEnv { if_doc = text "mkDsEnv"
                           , if_rec_types = KnotVars [mod] (\that_mod -> if that_mod == mod
                                                             then Just (return type_env)
                                                             else Nothing)
                           }
        if_lenv = mkIfLclEnv mod (text "CSL error in desugarer lookup in" <+> ppr mod)
        real_span = realSrcLocSpan (mkRealSrcLoc (moduleNameFS (moduleName mod)) 1 1)
        gbl_env = DsGblEnv { ds_mod = mod
                           , ds_gbl_rdr_env = rdr_env
                           , ds_name_ppr_ctx = mkNamePprCtx unit_env rdr_env
                           , ds_msgs = msg_var
                           , ds_if_env = (if_genv, if_lenv)
                           , ds_complete_matches = complete_matches
                           }
        lcl_env = DsLclEnv { dsl_loc = real_span }
  in (gbl_env, lcl_env)


{- *********************************************************************
*                                                                      *
                Operations in the monad
*                                                                      *
********************************************************************* -}

newSysLocalDs :: Type Zk -> DsM (Id Zk)
newSysLocalDs = mkSysLocalM (fsLit "ds")

putSrcSpanDs :: SrcSpan -> DsM a -> DsM a
putSrcSpanDs (UnhelpfulSpan {}) thing_inside = thing_inside
putSrcSpanDs (RealSrcSpan real_span _) thing_inside
  = updLclEnv (\env -> env { dsl_loc = real_span }) thing_inside

putSrcSpanDsA :: EpAnn ann -> DsM a -> DsM a
putSrcSpanDsA loc = putSrcSpanDs (locA loc)
