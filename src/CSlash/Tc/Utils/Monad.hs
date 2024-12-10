{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}

module CSlash.Tc.Utils.Monad
  ( module CSlash.Tc.Utils.Monad
  , module CSlash.Tc.Types
  , module CSlash.Tc.Types.TcRef
  , module CSlash.Data.IOEnv
  ) where

import CSlash.Builtin.Names

import CSlash.Tc.Errors.Types
import CSlash.Tc.Types     -- Re-export all
import CSlash.Tc.Types.Constraint
-- import GHC.Tc.Types.Evidence
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.TcRef
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Zonk.TcType

import CSlash.Cs hiding (LIE)

import CSlash.Unit
import CSlash.Unit.Env
import CSlash.Unit.External
import CSlash.Unit.Module.Warnings
import CSlash.Unit.Home.ModInfo

import CSlash.Core.UsageEnv
-- import GHC.Core.Multiplicity
-- import GHC.Core.InstEnv
-- import GHC.Core.FamInstEnv

import CSlash.Driver.Env
import CSlash.Driver.Session
import CSlash.Driver.Config.Diagnostic

-- import GHC.Runtime.Context

import CSlash.Data.IOEnv -- Re-export all
import CSlash.Data.Bag
import CSlash.Data.FastString
import CSlash.Data.Maybe

import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Error
import CSlash.Utils.Panic
import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.Logger
import qualified CSlash.Data.Strict as Strict

import CSlash.Types.Error
import CSlash.Types.Fixity.Env
import CSlash.Types.Name.Reader
import CSlash.Types.Name
-- import GHC.Types.SafeHaskell
import CSlash.Types.Id
import CSlash.Types.TypeEnv
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Types.SrcLoc
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set
import CSlash.Types.Name.Ppr
import CSlash.Types.Unique.FM ( emptyUFM )
import CSlash.Types.Unique.Supply
-- import GHC.Types.Annotations
import CSlash.Types.Basic( TopLevelFlag{-, TypeOrKind(..)-} )
-- import GHC.Types.CostCentre.State
import CSlash.Types.SourceFile

-- import qualified GHC.LanguageExtensions as LangExt

import Data.IORef
import Control.Monad

import qualified Data.Map as Map
import CSlash.Driver.Env.KnotVars
import CSlash.Linker.Types
import CSlash.Types.Unique.DFM
import CSlash.Iface.Errors.Types
import CSlash.Iface.Errors.Ppr
import CSlash.Tc.Types.LclEnv

{- *********************************************************************
*                                                                      *
                initTc
*                                                                      *
********************************************************************* -}

initTc
  :: CsEnv
  -> CsSource
  -> Bool
  -> Module
  -> RealSrcSpan
  -> TcM r
  -> IO (Messages TcRnMessage, Maybe r)
initTc cs_env cs_src keep_rn_syntax mod loc do_this = do
  keep_var <- newIORef emptyNameSet
  used_gre_var <- newIORef []
  infer_var <- newIORef True
  infer_reasons_var <- newIORef emptyMessages
  dfun_n_var <- newIORef emptyOccSet
  let type_env_var = cs_type_env_vars cs_env
  next_wrapper_num <- newIORef emptyModuleEnv
  let !dflags = cs_dflags cs_env
      !mhome_unit = cs_home_unit_maybe cs_env
      !logger = cs_logger cs_env

      maybe_rn_syntax :: a -> Maybe a
      maybe_rn_syntax empty_val
        | logHasDumpFlag logger Opt_D_dump_rn_ast = Just empty_val
        | gopt Opt_WriteHie dflags = Just empty_val
        | keep_rn_syntax = Just empty_val
        | otherwise = Nothing

      gbl_env = TcGblEnv
                { tcg_mod = mod
                , tcg_src = cs_src
                , tcg_rdr_env = emptyGlobalRdrEnv
                , tcg_default = if moduleUnit mod == primUnit
                                then Just [] else Nothing
                , tcg_fix_env = emptyNameEnv
                , tcg_type_env = emptyNameEnv
                , tcg_type_env_var = type_env_var
                , tcg_exports = []
                , tcg_imports = emptyImportAvails
                , tcg_dus = emptyDUs
                , tcg_used_gres = used_gre_var
                , tcg_keep = keep_var
                , tcg_dfun_n = dfun_n_var
                , tcg_merged = []
                , tcg_rn_exports = maybe_rn_syntax []
                , tcg_rn_imports = []
                , tcg_rn_decls = maybe_rn_syntax emptyRnGroup
                , tcg_tr_module = Nothing
                , tcg_binds = emptyLCsBinds
                , tcg_sigs = emptyNameSet
                , tcg_tcs = []
                , tcg_ksigs = emptyNameSet
                                      
                , tcg_hdr_info = Nothing
                                      
                , tcg_pc = False
                                      
                , tcg_main = Nothing
                                      
                , tcg_top_loc = loc
                                      
                , tcg_complete_matches = []
                }                     
  initTcWithGbl cs_env gbl_env loc do_this

initTcWithGbl
  :: CsEnv
  -> TcGblEnv
  -> RealSrcSpan
  -> TcM r
  -> IO (Messages TcRnMessage, Maybe r)
initTcWithGbl cs_env gbl_env loc do_this = do
  lie_var <- newIORef emptyWC
  errs_var <- newIORef emptyMessages
  usage_var <- newIORef zeroUE
  let lcl_env = TcLclEnv
                { tcl_lcl_ctxt = TcLclCtxt
                                 { tcl_loc = loc
                                 , tcl_ctxt = []
                                 , tcl_rdr = emptyLocalRdrEnv
                                 , tcl_env = emptyNameEnv
                                 , tcl_bndrs = []
                                 , tcl_tclvl = topTcLevel
                                 }
                , tcl_usage = usage_var
                , tcl_lie = lie_var
                , tcl_errs = errs_var
                }
  maybe_res <- initTcRnIf 'a' cs_env gbl_env lcl_env $ do
    r <- tryM do_this
    case r of
      Right res -> return $ Just res
      Left _ -> return Nothing

  lie <- readIORef (tcl_lie lcl_env)
  when (isJust maybe_res && not (isEmptyWC lie))
    $ pprPanic "initTc: unsolved constraints" (ppr lie)

  msgs <- readIORef $ tcl_errs lcl_env

  let final_res | errorsFound msgs = Nothing
                | otherwise = maybe_res

  return (msgs, final_res)

{- *********************************************************************
*                                                                      *
                Initialisation
*                                                                      *
********************************************************************* -}

initTcRnIf :: Char -> CsEnv -> gbl -> lcl -> TcRnIf gbl lcl a -> IO a
initTcRnIf uniq_tag cs_env gbl_env lcl_env thing_inside =
  let env = Env { env_top = cs_env
                , env_ut = uniq_tag
                , env_gbl = gbl_env
                , env_lcl = lcl_env
                } 
  in runIOEnv env thing_inside

{- *********************************************************************
*                                                                      *
                Simple accessors
*                                                                      *
********************************************************************* -}

discardResult :: TcM a -> TcM ()
discardResult a = a >> return ()

getTopEnv :: TcRnIf gbl lcl CsEnv
getTopEnv = do { env <- getEnv; return (env_top env) }

updTopEnv :: (CsEnv -> CsEnv) -> TcRnIf gbl lcl a -> TcRnIf gbl lcl a
updTopEnv upd = updEnv (\env@(Env { env_top = top }) -> env { env_top = upd top })

getGblEnv :: TcRnIf gbl lcl gbl
getGblEnv = do
  Env{..} <- getEnv
  return env_gbl

updGblEnv :: (gbl -> gbl) -> TcRnIf gbl lcl a -> TcRnIf gbl lcl a
updGblEnv upd = updEnv (\env@(Env { env_gbl = gbl }) -> env { env_gbl = upd gbl })

setGblEnv :: gbl' -> TcRnIf gbl' lcl a -> TcRnIf gbl lcl a
setGblEnv gbl_env = updEnv (\ env -> env { env_gbl = gbl_env })

getLclEnv :: TcRnIf gbl lcl lcl
getLclEnv = do { Env{..} <- getEnv; return env_lcl }

updLclEnv :: (lcl -> lcl) -> TcRnIf gbl lcl a -> TcRnIf gbl lcl a
updLclEnv upd = updEnv (\ env@(Env { env_lcl = lcl }) ->
                          env { env_lcl = upd lcl })

updLclCtxt :: (TcLclCtxt -> TcLclCtxt) -> TcRnIf gbl TcLclEnv a -> TcRnIf gbl TcLclEnv a
updLclCtxt upd = updLclEnv (modifyLclCtxt upd)

setLclEnv :: lcl' -> TcRnIf gbl lcl' a -> TcRnIf gbl lcl a
setLclEnv lcl_env = updEnv (\env -> env { env_lcl = lcl_env })

restoreLclEnv :: TcLclEnv -> TcRnIf gbl TcLclEnv a -> TcRnIf gbl TcLclEnv a
restoreLclEnv new_lcl_env = updLclEnv upd
  where
    upd old_lcl_env =  new_lcl_env { tcl_errs  = tcl_errs  old_lcl_env
                                   -- , tcl_lie   = tcl_lie   old_lcl_env
                                   , tcl_usage = tcl_usage old_lcl_env }

getEnvs :: TcRnIf gbl lcl (gbl, lcl)
getEnvs = do { env <- getEnv; return (env_gbl env, env_lcl env) }

setEnvs :: (gbl', lcl') -> TcRnIf gbl' lcl' a -> TcRnIf gbl lcl a
setEnvs (gbl_env, lcl_env) = setGblEnv gbl_env . setLclEnv lcl_env

updEnvs :: ((gbl,lcl) -> (gbl, lcl)) -> TcRnIf gbl lcl a -> TcRnIf gbl lcl a
updEnvs upd_envs = updEnv upd
  where
    upd env@(Env { env_gbl = gbl, env_lcl = lcl })
      = env { env_gbl = gbl', env_lcl = lcl' }
      where
        !(gbl', lcl') = upd_envs (gbl, lcl)

restoreEnvs :: (TcGblEnv, TcLclEnv) -> TcRn a -> TcRn a
restoreEnvs (gbl, lcl) = setGblEnv gbl . restoreLclEnv lcl

doptM :: DumpFlag -> TcRnIf gbl lcl Bool
doptM flag = do
  logger <- getLogger
  return (logHasDumpFlag logger flag)

goptM :: GeneralFlag -> TcRnIf gbl lcl Bool
goptM flag = gopt flag <$> getDynFlags

woptM :: WarningFlag -> TcRnIf gbl lcl Bool
woptM flag = wopt flag <$> getDynFlags

whenDOptM :: DumpFlag -> TcRnIf gbl lcl () -> TcRnIf gbl lcl ()
whenDOptM flag thing_inside = do
  b <- doptM flag
  when b thing_inside
{-# INLINE whenDOptM #-}

whenWOptM :: WarningFlag -> TcRnIf gbl lcl () -> TcRnIf gbl lcl ()
whenWOptM flag thing_inside = do
  b <- woptM flag
  when b thing_inside
{-# INLINE whenWOptM #-}

getEpsVar :: TcRnIf gbl lcl (TcRef ExternalPackageState)
getEpsVar = do
  env <- getTopEnv
  return (euc_eps (ue_eps (cs_unit_env env)))

getEps :: TcRnIf gbl lcl ExternalPackageState
getEps = do
  env <- getTopEnv
  liftIO $ csEPS env

updateEps :: (ExternalPackageState -> (ExternalPackageState, a)) -> TcRnIf gbl lcl a
updateEps upd = do
  traceIf (text "updating EPS")
  eps_var <- getEpsVar
  atomicUpdMutVar' eps_var upd

updateEps_ :: (ExternalPackageState -> ExternalPackageState) -> TcRnIf gbl lcl ()
updateEps_ upd = updateEps (\eps -> (upd eps, ()))

getHpt :: TcRnIf gbl lcl HomePackageTable
getHpt = do
  env <- getTopEnv
  return (cs_HPT env)

getEpsAndHug :: TcRnIf gbl lcl (ExternalPackageState, HomeUnitGraph)
getEpsAndHug = do
  env <- getTopEnv
  eps <- liftIO $ csEPS env
  return (eps, cs_HUG env)

withIfaceErr :: MonadIO m => SDocContext -> m (MaybeErr MissingInterfaceError a) -> m a
withIfaceErr ctx do_this = do
  r <- do_this
  case r of
    Failed err -> do
      let opts = defaultDiagnosticOpts @IfaceMessage
          msg = missingInterfaceErrorDiagnostic opts err
      liftIO $ throwCsExceptionIO (ProgramError (renderWithContext ctx msg))
    Succeeded result -> return result

{- *********************************************************************
*                                                                      *
                Unique supply
*                                                                      *
********************************************************************* -}

newUnique :: TcRnIf gbl lcl Unique
newUnique = do
  env <- getEnv
  let tag = env_ut env
  liftIO $! uniqFromTag tag

newSysName :: OccName -> TcRnIf gbl lcl Name
newSysName occ = do
  uniq <- newUnique
  return $ mkSystemName uniq occ

{- *********************************************************************
*                                                                      *
                Debugging
*                                                                      *
********************************************************************* -}

traceTc :: String -> SDoc -> TcRn ()
traceTc herald doc = labelledTraceOptTcRn Opt_D_dump_tc_trace herald doc
{-# INLINE traceTc #-}

traceRn :: String -> SDoc -> TcRn ()
traceRn herald doc = labelledTraceOptTcRn Opt_D_dump_rn_trace herald doc
{-# INLINE traceRn #-}

labelledTraceOptTcRn :: DumpFlag -> String -> SDoc -> TcRn ()
labelledTraceOptTcRn flag herald doc = traceOptTcRn flag (formatTraceMsg herald doc)
{-# INLINE labelledTraceOptTcRn #-}

formatTraceMsg :: String -> SDoc -> SDoc
formatTraceMsg herald doc = hang (text herald) 2 doc

traceOptTcRn :: DumpFlag -> SDoc -> TcRn ()
traceOptTcRn flag doc =
  whenDOptM flag $
    dumpTcRn False flag "" FormatText doc
{-# INLINE traceOptTcRn #-}

dumpOptTcRn :: DumpFlag -> String -> DumpFormat -> SDoc -> TcRn ()
dumpOptTcRn flag title fmt doc =
  whenDOptM flag $ dumpTcRn False flag title fmt doc
{-# INLINE dumpOptTcRn #-}

dumpTcRn :: Bool -> DumpFlag -> String -> DumpFormat -> SDoc -> TcRn ()
dumpTcRn useUserStyle flag title fmt doc = do
  logger <- getLogger
  name_ppr_ctx <- getNamePprCtx
  real_doc <- wrapDocLoc doc
  let sty = if useUserStyle
              then mkUserStyle name_ppr_ctx AllTheWay
              else mkDumpStyle name_ppr_ctx
  liftIO $ logDumpFile logger sty flag title fmt real_doc

wrapDocLoc :: SDoc -> TcRn SDoc
wrapDocLoc doc = do
  logger <- getLogger
  if logHasDumpFlag logger Opt_D_ppr_debug
    then do loc <- getSrcSpanM
            return $ mkLocMessage MCOutput loc doc
    else return doc

getNamePprCtx :: TcRn NamePprCtx
getNamePprCtx = do
  rdr_env <- getGlobalRdrEnv
  cs_env <- getTopEnv
  return $ mkNamePprCtx (cs_unit_env cs_env) rdr_env

traceIf :: SDoc -> TcRnIf m n ()
traceIf = traceOptIf Opt_D_dump_if_trace
{-# INLINE traceIf #-}

traceOptIf :: DumpFlag -> SDoc -> TcRnIf m n ()
traceOptIf flag doc = whenDOptM flag $ do
  logger <- getLogger
  liftIO (putMsg logger doc)

{- *********************************************************************
*                                                                      *
                Typechecker global environment
*                                                                      *
********************************************************************* -}

getGlobalRdrEnv :: TcRn GlobalRdrEnv
getGlobalRdrEnv = do
  env <- getGblEnv
  return (tcg_rdr_env env)

getRdrEnvs :: TcRn (GlobalRdrEnv, LocalRdrEnv)
getRdrEnvs = do
  (gbl, lcl) <- getEnvs
  return (tcg_rdr_env gbl, getLclEnvRdrEnv lcl)

getImports :: TcRn ImportAvails
getImports = do
  env <- getGblEnv
  return $ tcg_imports env

getFixityEnv :: TcRn FixityEnv
getFixityEnv = do
  env <- getGblEnv
  return $ tcg_fix_env env

extendFixityEnv :: [(Name, FixItem)] -> RnM a -> RnM a
extendFixityEnv new_bit
  = updGblEnv $ \env@(TcGblEnv { tcg_fix_env = old_fix_env }) ->
                  env { tcg_fix_env = extendNameEnvList old_fix_env new_bit }

{- *********************************************************************
*                                                                      *
                Error management
*                                                                      *
********************************************************************* -}

getSrcSpanM :: TcRn SrcSpan
getSrcSpanM = do
  env <- getLclEnv
  return $ RealSrcSpan (getLclEnvLoc env) Strict.Nothing

setSrcSpan :: SrcSpan -> TcRn a -> TcRn a
setSrcSpan (RealSrcSpan loc _) thing_inside
  = updLclCtxt (\env -> env { tcl_loc = loc }) thing_inside
setSrcSpan loc@(UnhelpfulSpan _) thing_inside
  | isGeneratedSrcSpan loc
  = panic "setSrcSpan: isGeneratedSrcSpan"
  | otherwise
  = thing_inside

setSrcSpanA :: EpAnn ann -> TcRn a -> TcRn a
setSrcSpanA l = setSrcSpan (locA l)

addLocM :: (HasLoc t) => (a -> TcM b) -> GenLocated t a -> TcM b
addLocM fn (L loc a) = setSrcSpan (getHasLoc loc) $ fn a

wrapLocMA :: (a -> TcM b) -> GenLocated (EpAnn ann) a -> TcRn (GenLocated (EpAnn ann) b)
wrapLocMA fn (L loc a) = setSrcSpanA loc $ do
  b <- fn a
  return (L loc b)

wrapLocFstMA :: (a -> TcM (b, c)) -> GenLocated (EpAnn ann) a -> TcM (GenLocated (EpAnn ann) b, c)
wrapLocFstMA fn (L loc a) = setSrcSpanA loc $ do
  (b, c) <- fn a
  return (L loc b, c)

setErrsVar :: TcRef (Messages TcRnMessage) -> TcRn a -> TcRn a
setErrsVar v = updLclEnv $ \env -> env { tcl_errs = v }

getErrsVar :: TcRn (TcRef (Messages TcRnMessage))
getErrsVar = do
  env <- getLclEnv
  return (tcl_errs env)

addErr :: TcRnMessage -> TcRn ()
addErr msg = do
  loc <- getSrcSpanM
  addErrAt loc msg

addErrAt :: SrcSpan -> TcRnMessage -> TcRn ()
addErrAt loc msg = do
  ctxt <- getErrCtxt
  tidy_env <- liftZonkM tcInitTidyEnv
  err_info <- mkErrInfo tidy_env ctxt
  let detailed_msg = mkDetailedMessage (ErrInfo err_info Outputable.empty) msg
  add_long_err_at loc detailed_msg

mkDetailedMessage :: ErrInfo -> TcRnMessage -> TcRnMessageDetailed
mkDetailedMessage = TcRnMessageDetailed

checkErr :: Bool -> TcRnMessage -> TcRn ()
checkErr ok msg = unless ok (addErr msg)

addMessages :: Messages TcRnMessage -> TcRn ()
addMessages msgs1 = do
  errs_var <- getErrsVar
  msgs0 <- readTcRef errs_var
  writeTcRef errs_var (msgs0 `unionMessages` msgs1)

{- *********************************************************************
*                                                                      *
        Shared error message stuff: renamer and typechecker
*                                                                      *
********************************************************************* -}

add_long_err_at :: SrcSpan -> TcRnMessageDetailed -> TcRn ()
add_long_err_at loc msg = mk_long_err_at loc msg >>= reportDiagnostic
  where
    mk_long_err_at :: SrcSpan -> TcRnMessageDetailed -> TcRn (MsgEnvelope TcRnMessage)
    mk_long_err_at loc msg = do
      name_ppr_ctx <- getNamePprCtx
      unit_state <- cs_units <$> getTopEnv
      return $ mkErrorMsgEnvelope loc name_ppr_ctx $ TcRnMessageWithInfo unit_state msg

mkTcRnMessage :: SrcSpan -> TcRnMessage -> TcRn (MsgEnvelope TcRnMessage)
mkTcRnMessage loc msg = do
  name_ppr_ctx <- getNamePprCtx
  diag_opts <- initDiagOpts <$> getDynFlags
  return $ mkMsgEnvelope diag_opts loc name_ppr_ctx msg

reportDiagnostic :: MsgEnvelope TcRnMessage -> TcRn ()
reportDiagnostic msg = do
  traceTc "Adding diagnostic:" (pprLocMsgEnvelopeDefault msg)
  errs_var <- getErrsVar
  msgs <- readTcRef errs_var
  writeTcRef errs_var (msg `addMessage` msgs)

checkNoErrs :: TcM r -> TcM r
checkNoErrs main = do
  (res, no_errs) <- askNoErrs main
  unless no_errs failM
  return res

ifErrsM :: TcRn r -> TcRn r -> TcRn r
ifErrsM bale_out normal = do
  errs_var <- getErrsVar
  msgs <- readTcRef errs_var
  if errorsFound msgs then bale_out else normal

failIfErrsM :: TcRn ()
failIfErrsM = ifErrsM failM (return ())

{- *********************************************************************
*                                                                      *
        Context management for the type checker
*                                                                      *
********************************************************************* -}

getErrCtxt :: TcM [ErrCtxt]
getErrCtxt = do
  env <- getLclEnv
  return $ getLclEnvErrCtxt env

addErrCtxt :: SDoc -> TcM a -> TcM a
addErrCtxt msg = addErrCtxtM (\env -> return (env, msg))
{-# INLINE addErrCtxt #-}

addErrCtxtM :: (TidyEnv -> ZonkM (TidyEnv, SDoc)) -> TcM a -> TcM a
addErrCtxtM ctxt = pushCtxt (False, ctxt)
{-# INLINE addErrCtxtM #-}

pushCtxt :: ErrCtxt -> TcM a -> TcM a
pushCtxt ctxt = updLclEnv (updCtxt ctxt)
{-# INLINE pushCtxt #-}

updCtxt :: ErrCtxt -> TcLclEnv -> TcLclEnv
updCtxt  ctxt env = addLclEnvErrCtxt ctxt env
 
getCtLocM :: CtOrigin -> TcM CtLoc
getCtLocM origin = do
  env <- getLclEnv
  return $ CtLoc { ctl_origin = origin
                 , ctl_env = mkCtLocEnv env
                 , ctl_depth = initialSubGoalDepth }

mkCtLocEnv :: TcLclEnv -> CtLocEnv
mkCtLocEnv lcl_env = CtLocEnv { ctl_bndrs = getLclEnvBinderStack lcl_env
                              , ctl_ctxt = getLclEnvErrCtxt lcl_env
                              , ctl_loc = getLclEnvLoc lcl_env
                              , ctl_tclvl = getLclEnvTcLevel lcl_env
                              , ctl_rdr = getLclEnvRdrEnv lcl_env
                              }

{- *********************************************************************
*                                                                      *
             Error recovery and exceptions
*                                                                      *
********************************************************************* -}

tcTryM :: TcRn r -> TcRn (Maybe r)
tcTryM thing_inside = do
  either_res <- tryM thing_inside
  return $ case either_res of
             Left _ -> Nothing
             Right r -> Just r

capture_messages :: TcM r -> TcM (r, Messages TcRnMessage)
capture_messages thing_inside = do
  msg_var <- newTcRef emptyMessages
  res <- setErrsVar msg_var thing_inside
  msgs <- readTcRef msg_var
  return (res, msgs)

askNoErrs :: TcRn a -> TcRn (a, Bool)
askNoErrs thing_inside = do
  (mb_res, msgs) <- capture_messages $ tcTryM thing_inside
  addMessages msgs
  case mb_res of
    Nothing -> failM
    Just res -> let errs_found = errorsFound msgs
                in return (res, not errs_found)

attemptM :: TcRn r -> TcRn (Maybe r)
attemptM thing_inside = do
  mb_r <- tcTryM thing_inside
  when (isNothing mb_r) $ traceTc "attemptM recovering with insoluble constraints" empty
  return mb_r

mapAndRecoverM :: (a -> TcRn b) -> [a] -> TcRn [b]
mapAndRecoverM f xs = do
  mb_rs <- mapM (attemptM . f) xs
  return [ r | Just r <- mb_rs ]

mapAndReportM :: (a -> TcRn b) -> [a] -> TcRn [b]
mapAndReportM  f xs = do
  mb_rs <- mapM (attemptM . f) xs
  when (any isNothing mb_rs) failM
  return [ r | Just r <- mb_rs ]

{- *********************************************************************
*                                                                      *
             Error message generation (type checker)
*                                                                      *
********************************************************************* -}

addErrTc :: TcRnMessage -> TcM ()
addErrTc err_msg = do
  env0 <- liftZonkM tcInitTidyEnv
  addErrTcM (env0, err_msg)

addErrTcM :: (TidyEnv, TcRnMessage) -> TcM ()
addErrTcM (tidy_env, err_msg) = do
  ctxt <- getErrCtxt
  loc <- getSrcSpanM
  add_err_tcm tidy_env err_msg loc ctxt

failWithTc :: TcRnMessage -> TcM a
failWithTc err_msg = addErrTc err_msg >> failM

no_err_info :: ErrInfo
no_err_info = ErrInfo Outputable.empty Outputable.empty

addTcRnDiagnostic :: TcRnMessage -> TcM ()
addTcRnDiagnostic msg = do
  loc <- getSrcSpanM
  mkTcRnMessage loc msg >>= reportDiagnostic

addDiagnostic :: TcRnMessage -> TcRn ()
addDiagnostic msg = add_diagnostic (mkDetailedMessage no_err_info msg)

addDiagnosticAt :: SrcSpan -> TcRnMessage -> TcRn ()
addDiagnosticAt loc msg = do
  unit_state <- cs_units <$> getTopEnv
  let detailed_msg = mkDetailedMessage no_err_info msg
  mkTcRnMessage loc (TcRnMessageWithInfo unit_state detailed_msg) >>= reportDiagnostic

add_diagnostic :: TcRnMessageDetailed -> TcRn ()
add_diagnostic msg = do
  loc <- getSrcSpanM
  unit_state <- cs_units <$> getTopEnv
  mkTcRnMessage loc (TcRnMessageWithInfo unit_state msg) >>= reportDiagnostic

add_err_tcm :: TidyEnv -> TcRnMessage -> SrcSpan -> [ErrCtxt] -> TcM ()
add_err_tcm tidy_env msg loc ctxt = do
  err_info <- mkErrInfo tidy_env ctxt
  add_long_err_at loc (mkDetailedMessage (ErrInfo err_info Outputable.empty) msg)

mkErrInfo :: TidyEnv -> [ErrCtxt] -> TcM SDoc
mkErrInfo env ctxts = go False 0 env ctxts
  where
    go :: Bool -> Int -> TidyEnv -> [ErrCtxt] -> TcM SDoc
    go _ _ _ [] = return empty
    go dbg n env ((is_landmark, ctxt) : ctxts)
      | is_landmark || n < mAX_CONTEXTS
      = do (env', msg) <- liftZonkM $ ctxt env
           let n' = if is_landmark then n else n + 1
           rest <- go dbg n' env' ctxts
           return (msg $$ rest)
      | otherwise
      = go dbg n env ctxts

mAX_CONTEXTS :: Int
mAX_CONTEXTS = 3

{- *********************************************************************
*                                                                      *
             Type constraints
*                                                                      *
********************************************************************* -}

getConstraintVar :: TcM (TcRef WantedConstraints)
getConstraintVar = do
  env <- getLclEnv
  return (tcl_lie env)

emitSimples :: Cts -> TcM ()
emitSimples cts = do
  lie_var <- getConstraintVar
  updTcRef lie_var (`addSimples` cts)

pushTcLevelM :: TcM a -> TcM (TcLevel, a)
pushTcLevelM thing_inside = do
  tclvl <- getTcLevel
  let tclvl' = pushTcLevel tclvl
  res <- updLclEnv (setLclEnvTcLevel tclvl') thing_inside
  return (tclvl', res)

getTcLevel :: TcM TcLevel
getTcLevel = do
  env <- getLclEnv
  return $! getLclEnvTcLevel env 

getLclTypeEnv :: TcM TcTypeEnv
getLclTypeEnv = do
  env <- getLclEnv
  return $ getLclEnvTypeEnv env

{- *********************************************************************
*                                                                      *
             Stuff for the renamer's local env
*                                                                      *
********************************************************************* -}

getLocalRdrEnv :: RnM LocalRdrEnv
getLocalRdrEnv = do
  env <- getLclEnv
  return $ getLclEnvRdrEnv env

{- *********************************************************************
*                                                                      *
             Stuff for interface decls
*                                                                      *
********************************************************************* -}

mkIfLclEnv :: Module -> SDoc -> IfLclEnv
mkIfLclEnv mod loc = IfLclEnv
  { if_mod = mod
  , if_loc = loc
  , if_nsubst = Nothing
  , if_implicits_env = Nothing
  , if_tv_env = emptyFsEnv
  , if_id_env = emptyFsEnv
  }

initIfaceTcRn :: IfG a -> TcRn a
initIfaceTcRn thing_inside = do
  tcg_env <- getGblEnv
  cs_env <- getTopEnv
  let !mhome_unit = cs_home_unit_maybe cs_env
      !knot_vars = tcg_type_env_var tcg_env
      is_instantiate = fromMaybe False (isHomeUnitInstantiating <$> mhome_unit)
      if_env = IfGblEnv { if_doc = text "initIfaceTcRn"
                        , if_rec_types = if is_instantiate
                                         then emptyKnotVars
                                         else readTcRef <$> knot_vars }
  setEnvs (if_env, ()) thing_inside                        

initIfaceLoad :: CsEnv -> IfG a -> IO a
initIfaceLoad cs_env do_this =
  let gbl_env = IfGblEnv { if_doc = text "initIfaceLoad"
                         , if_rec_types = emptyKnotVars }
  in initTcRnIf 'i' (cs_env { cs_type_env_vars = emptyKnotVars }) gbl_env () do_this
  

initIfaceCheck :: SDoc -> CsEnv -> IfG a -> IO a
initIfaceCheck doc cs_env do_this =
  let gbl_env = IfGblEnv
                { if_doc = text "initIfaceCheck" <+> doc
                , if_rec_types = readTcRef <$> cs_type_env_vars cs_env
                }
  in initTcRnIf 'i' cs_env gbl_env () do_this

initIfaceLcl :: Module -> SDoc -> IfL a -> IfM lcl a
initIfaceLcl mod loc_doc thing_inside =
  setLclEnv (mkIfLclEnv mod loc_doc) thing_inside

--------------------------------------------------------------------------------

liftZonkM :: ZonkM a -> TcM a
liftZonkM (ZonkM f) = do
  logger <- getLogger
  name_ppr_ctx <- getNamePprCtx
  lvl <- getTcLevel
  src_span <- getSrcSpanM
  bndrs <- getLclEnvBinderStack <$> getLclEnv
  let zge = ZonkGblEnv { zge_logger = logger
                       , zge_name_ppr_ctx = name_ppr_ctx
                       , zge_src_span = src_span
                       , zge_tc_level = lvl
                       , zge_binder_stack = bndrs }
  liftIO $ f zge
{-# INLINE liftZonkM #-}
