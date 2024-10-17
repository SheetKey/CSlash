module CSlash.Tc.Types where

import CSlash.Platform

import CSlash.Driver.Env
import CSlash.Driver.Env.KnotVars
-- import GHC.Driver.Config.Core.Lint
import CSlash.Driver.DynFlags
-- import {-# SOURCE #-} GHC.Driver.Hooks

import CSlash.Linker.Types

import CSlash.Cs

import CSlash.Tc.Utils.TcType
-- import GHC.Tc.Types.Constraint
-- import GHC.Tc.Types.Evidence
-- import GHC.Tc.Types.TH
-- import GHC.Tc.Types.TcRef
import CSlash.Tc.Types.LclEnv
-- import GHC.Tc.Types.BasicTypes
-- import GHC.Tc.Types.ErrCtxt
-- import {-# SOURCE #-} GHC.Tc.Errors.Hole.Plugin ( HoleFitPlugin )
-- import GHC.Tc.Errors.Types

-- import GHC.Core.Reduction ( Reduction(..) )
import CSlash.Core.Type
import CSlash.Core.TyCon  ( TyCon )
-- import GHC.Core.PatSyn ( PatSyn )
-- import GHC.Core.Lint   ( lintAxioms )
-- import GHC.Core.InstEnv
-- import GHC.Core.FamInstEnv
-- import GHC.Core.Predicate

import CSlash.Types.Fixity.Env
-- import GHC.Types.Annotations
import CSlash.Types.CompleteMatch
import CSlash.Types.Name.Reader
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set
import CSlash.Types.Avail
import CSlash.Types.Var
import CSlash.Types.TypeEnv
import CSlash.Types.SourceFile
import CSlash.Types.SrcLoc
import CSlash.Types.Unique.FM
import CSlash.Types.Basic
-- import GHC.Types.CostCentre.State
import CSlash.Types.PcInfo

import CSlash.Data.IOEnv
import CSlash.Data.Bag
import CSlash.Data.List.SetOps

import CSlash.Unit
import CSlash.Unit.Module.Warnings
import CSlash.Unit.Module.Deps
import CSlash.Unit.Module.ModDetails

import CSlash.Utils.Error
import CSlash.Utils.Outputable
import CSlash.Utils.Fingerprint
import CSlash.Utils.Panic
import CSlash.Utils.Logger

-- import CSlash.Builtin.Names ( isUnboundName )

-- import GHCi.Message
-- import GHCi.RemoteTypes

import Data.Set      ( Set )
import qualified Data.Set as S
import Data.Dynamic  ( Dynamic )
import Data.Map ( Map )
import Data.Typeable ( TypeRep )
import Data.Maybe    ( mapMaybe )

data NameShape = NameShape
  { ns_mod_name :: ModuleName
  , ns_exports :: [AvailInfo]
  , ns_map :: OccEnv Name
  }

{- *********************************************************************
*                                                                      *
               Standard monad definition for TcRn
*                                                                      *
********************************************************************* -}

type TcRnIf a b = IOEnv (Env a b)
type TcRn = TcRnIf TcGblEnv TcLclEnv

type IfM lcl = TcRnIf IfGblEnv lcl
type IfG = IfM ()
type IfL = IfM IfLclEnv

data Env gbl lcl = Env
  { env_top :: !CsEnv
  , env_ut :: {-# UNPACK #-} !Char
  , env_gbl :: gbl
  , env_lcl :: lcl
  }

instance ContainsDynFlags (Env gbl lcl) where
  extractDynFlags env = cs_dflags (env_top env)

instance ContainsLogger (Env gbl lcl) where
    extractLogger env = cs_logger (env_top env)

-- instance ContainsModule gbl => ContainsModule (Env gbl lcl) where
--     extractModule env = extractModule (env_gbl env)

{- *********************************************************************
*                                                                      *
                The interface environments
              Used when dealing with IfaceDecls
*                                                                      *
********************************************************************* -}  

data IfGblEnv = IfGblEnv
  { if_doc :: SDoc
  , if_rec_types :: (KnotVars (IfG TypeEnv))
  }

data IfLclEnv = IfLclEnv
  { if_mod :: !Module
  , if_loc :: SDoc
  , if_nsubst :: Maybe NameShape
  , if_implicits_env :: Maybe TypeEnv
  , if_tv_env :: FastStringEnv TypeVar
  , if_id_env :: FastStringEnv Id
  }

{- *********************************************************************
*                                                                      *
                Global typechecker environment
*                                                                      *
********************************************************************* -}

data FrontendResult = FrontendTypecheck TcGblEnv

data TcGblEnv
