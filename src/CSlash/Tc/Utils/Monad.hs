{-# LANGUAGE RecordWildCards #-}

module CSlash.Tc.Utils.Monad
  ( module CSlash.Tc.Utils.Monad
  , module CSlash.Tc.Types
  , module CSlash.Data.IOEnv
  ) where

import CSlash.Builtin.Names

-- import GHC.Tc.Errors.Types
import CSlash.Tc.Types     -- Re-export all
-- import GHC.Tc.Types.Constraint
-- import GHC.Tc.Types.Evidence
import GHC.Tc.Types.Origin
import CSlash.Tc.Types.TcRef
import GHC.Tc.Utils.TcType
-- import GHC.Tc.Zonk.TcType

import CSlash.Cs hiding (LIE)

import CSlash.Unit
import CSlash.Unit.Env
import CSlash.Unit.External
import CSlash.Unit.Module.Warnings
import CSlash.Unit.Home.ModInfo

-- import GHC.Core.UsageEnv
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
-- import CSlash.Types.Name.Ppr
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
-- import CSlash.Iface.Errors.Types
-- import GHC.Iface.Errors.Ppr
import CSlash.Tc.Types.LclEnv

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

setLclEnv :: lcl' -> TcRnIf gbl lcl' a -> TcRnIf gbl lcl a
setLclEnv lcl_env = updEnv (\env -> env { env_lcl = lcl_env })

doptM :: DumpFlag -> TcRnIf gbl lcl Bool
doptM flag = do
  logger <- getLogger
  return (logHasDumpFlag logger flag)

goptM :: GeneralFlag -> TcRnIf gbl lcl Bool
goptM flag = gopt flag <$> getDynFlags

whenDOptM :: DumpFlag -> TcRnIf gbl lcl () -> TcRnIf gbl lcl ()
whenDOptM flag thing_inside = do
  b <- doptM flag
  when b thing_inside

getEpsVar :: TcRnIf gbl lcl (TcRef ExternalPackageState)
getEpsVar = do
  env <- getTopEnv
  return (euc_eps (ue_eps (cs_unit_env env)))

updateEps :: (ExternalPackageState -> (ExternalPackageState, a)) -> TcRnIf gbl lcl a
updateEps upd = do
  traceIf (text "updating EPS")
  eps_var <- getEpsVar
  atomicUpdMutVar' eps_var upd

updateEps_ :: (ExternalPackageState -> ExternalPackageState) -> TcRnIf gbl lcl ()
updateEps_ upd = updateEps (\eps -> (upd eps, ()))

getEpsAndHug :: TcRnIf gbl lcl (ExternalPackageState, HomeUnitGraph)
getEpsAndHug = do
  env <- getTopEnv
  eps <- liftIO $ csEPS env
  return (eps, cs_HUG env)

{- *********************************************************************
*                                                                      *
                Debugging
*                                                                      *
********************************************************************* -}

traceIf :: SDoc -> TcRnIf m n ()
traceIf = traceOptIf Opt_D_dump_if_trace
{-# INLINE traceIf #-}

traceOptIf :: DumpFlag -> SDoc -> TcRnIf m n ()
traceOptIf flag doc = whenDOptM flag $ do
  logger <- getLogger
  liftIO (putMsg logger doc)

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
