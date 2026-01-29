module CSlash.Iface.Make where

import CSlash.Cs

-- import GHC.Stg.InferTags.TagSig (StgCgInfos)
-- import GHC.StgToCmm.Types (CmmCgInfos (..))

import CSlash.Tc.Utils.TcType
import CSlash.Tc.Utils.Monad

-- import CSlash.Iface.Decl
import CSlash.Iface.Syntax
import CSlash.Iface.Recomp
import CSlash.Iface.Load
-- import GHC.Iface.Ext.Fields

-- import GHC.CoreToIface

-- import qualified GHC.LanguageExtensions as LangExt
import CSlash.Core
-- import GHC.Core.Class
-- import GHC.Core.Coercion.Axiom
import CSlash.Core.ConLike
-- import GHC.Core.InstEnv
-- import GHC.Core.FamInstEnv
import CSlash.Core.Ppr
-- import GHC.Core.RoughMap( RoughMatchTc(..) )

-- import GHC.Driver.Config.HsToCore.Usage
import CSlash.Driver.Env
import CSlash.Driver.Backend
import CSlash.Driver.DynFlags
-- import GHC.Driver.Plugins

import CSlash.Types.Var.Id
import CSlash.Types.Fixity.Env
-- import GHC.Types.SafeHaskell
-- import GHC.Types.Annotations
import CSlash.Types.Name
import CSlash.Types.Avail
import CSlash.Types.Name.Reader
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set
import CSlash.Types.Unique.DSet
import CSlash.Types.TypeEnv
import CSlash.Types.SourceFile
import CSlash.Types.TyThing
import CSlash.Types.PcInfo
import CSlash.Types.CompleteMatch
import CSlash.Types.SourceText
import CSlash.Types.SrcLoc ( unLoc )

import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Logger

import CSlash.Data.FastString
import CSlash.Data.Maybe

-- import GHC.HsToCore.Docs
-- import GHC.HsToCore.Usage

import CSlash.Unit
import CSlash.Unit.Module.Warnings
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.ModDetails
import CSlash.Unit.Module.ModGuts
import CSlash.Unit.Module.ModSummary
import CSlash.Unit.Module.Deps

import Data.Function
import Data.List ( sortBy )
import Data.Ord
import Data.IORef

{- *********************************************************************
*                                                                      *
            Completing an interface
*                                                                      *
********************************************************************* -}

mkFullIface :: CsEnv -> PartialModIface -> Maybe a -> Maybe a -> IO ModIface
mkFullIface = panic "mkFullIface"
