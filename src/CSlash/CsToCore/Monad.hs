{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

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
import CSlash.CsToCore.Pmc.Solver.Types (Nablas, initNablas)

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
import Control.Monad (unless)

{- *********************************************************************
*                                                                      *
                Data types for the desugarer
*                                                                      *
********************************************************************* -}

data DsMatchContext = DsMatchContext CsMatchContextRn SrcSpan

instance Outputable DsMatchContext where
  ppr (DsMatchContext cs_match ss) = ppr ss <+> pprMatchContext cs_match

data EquationInfo
  = EqnMatch { eqn_pat :: LPat Zk
             , eqn_rest :: EquationInfo }
  | EqnDone (MatchResult CoreExpr)

type EquationInfoNE = EquationInfo

prependPats :: [LPat Zk] -> EquationInfo -> EquationInfo
prependPats [] eqn = eqn
prependPats (pat:pats) eqn = EqnMatch { eqn_pat = pat, eqn_rest = prependPats pats eqn }

mkEqnInfo :: [LPat Zk] -> MatchResult CoreExpr -> EquationInfo
mkEqnInfo pats = prependPats pats . EqnDone

eqnMatchResult :: EquationInfo -> MatchResult CoreExpr
eqnMatchResult (EqnDone rhs) = rhs
eqnMatchResult (EqnMatch { eqn_rest = eq }) = eqnMatchResult eq

instance Outputable EquationInfo where
  ppr = ppr . allEqnPats where
    allEqnPats (EqnDone {}) = []
    allEqnPats (EqnMatch { eqn_pat = pat, eqn_rest = eq }) = unLoc pat : allEqnPats eq

type DsWrapper = CoreExpr -> CoreExpr

idDsWrapper :: DsWrapper
idDsWrapper e = e

data MatchResult a
  = MR_Infallible (DsM a)
  | MR_Fallible (CoreExpr -> DsM a)
  deriving Functor

instance Applicative MatchResult where
  pure v = MR_Infallible (pure v)
  MR_Infallible f <*> MR_Infallible x = MR_Infallible (f <*> x)
  f <*> x = MR_Fallible $ \fail -> runMatchResult fail f <*> runMatchResult fail x

runMatchResult :: CoreExpr -> MatchResult a -> DsM a
runMatchResult fail = \case
  MR_Infallible body -> body
  MR_Fallible body_fn -> body_fn fail

{-**********************************************************************
*                                                                      *
           Monad functions
*                                                                      *
**********************************************************************-}


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
  unless (null ds_complete_matches) $
    pprPanic "ds_complete_matches" (ppr ds_complete_matches)

  return $ mkDsEnvs unit_env this_mod rdr_env type_env msg_var

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

initTcDsForSolver :: TcM a -> DsM a
initTcDsForSolver thing_inside = do
  (gbl, lcl) <- getEnvs
  cs_env <- getTopEnv
  let DsGblEnv { ds_mod = mod
               , ds_gbl_rdr_env = rdr_env
               } = gbl
      DsLclEnv { dsl_loc = loc } = lcl

  (msgs, mb_ret) <- liftIO $ initTc cs_env CsSrcFile False mod loc $
    updGblEnv (\tc_gbl -> tc_gbl { tcg_rdr_env = rdr_env }) $ thing_inside
  case mb_ret of
    Just ret -> pure ret
    Nothing -> pprPanic "initTcDsForSolver"
               (vcat $ pprMsgEnvelopeBagWithLocDefault (getErrorMessages msgs))

mkDsEnvs
  :: UnitEnv
  -> Module
  -> GlobalRdrEnv
  -> TypeEnv
  -> IORef (Messages DsMessage)
  -> (DsGblEnv, DsLclEnv)
mkDsEnvs unit_env mod rdr_env type_env msg_var 
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
                           }
        lcl_env = DsLclEnv { dsl_loc = real_span
                           , dsl_nablas = initNablas }
  in (gbl_env, lcl_env)


{- *********************************************************************
*                                                                      *
                Operations in the monad
*                                                                      *
********************************************************************* -}

newFailLocalMDs :: Type Zk -> DsM (Id Zk)
newFailLocalMDs = mkSysLocalM (fsLit "fail")

newSysLocalMDs :: Type Zk -> DsM (Id Zk)
newSysLocalMDs = mkSysLocalM (fsLit "ds")

newSysLocalDs :: Type Zk -> DsM (Id Zk)
newSysLocalDs = mkSysLocalM (fsLit "ds")

newSysLocalsDs :: [Type Zk] -> DsM [Id Zk]
newSysLocalsDs = mapM newSysLocalDs

getPmNablas :: DsM Nablas
getPmNablas = do
  env <- getLclEnv
  return (dsl_nablas env) 

updPmNablas :: Nablas -> DsM a -> DsM a
updPmNablas nablas = updLclEnv (\env -> env { dsl_nablas = nablas })

getSrcSpanDs :: DsM SrcSpan
getSrcSpanDs = do
  env <- getLclEnv
  return $ RealSrcSpan (dsl_loc env) Strict.Nothing

putSrcSpanDs :: SrcSpan -> DsM a -> DsM a
putSrcSpanDs (UnhelpfulSpan {}) thing_inside = thing_inside
putSrcSpanDs (RealSrcSpan real_span _) thing_inside
  = updLclEnv (\env -> env { dsl_loc = real_span }) thing_inside

putSrcSpanDsA :: EpAnn ann -> DsM a -> DsM a
putSrcSpanDsA loc = putSrcSpanDs (locA loc)

mkNamePprCtxDs :: DsM NamePprCtx
mkNamePprCtxDs = ds_name_ppr_ctx <$> getGblEnv
