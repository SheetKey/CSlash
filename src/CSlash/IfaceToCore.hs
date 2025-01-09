module CSlash.IfaceToCore where

import CSlash.Driver.Env
import CSlash.Driver.Session
-- import GHC.Driver.Config.Core.Lint ( initLintConfig )

-- import GHC.Builtin.Types.Literals(typeNatCoAxiomRules)
import CSlash.Builtin.Types

-- import GHC.Iface.Decl (toIfaceBooleanFormula)
import CSlash.Iface.Syntax
import CSlash.Iface.Load
import CSlash.Iface.Env

-- import GHC.StgToCmm.Types
-- import GHC.Runtime.Heap.Layout

import CSlash.Tc.Errors.Types
-- import GHC.Tc.TyCl.Build
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Utils.TcType

import CSlash.Core.Type
-- import GHC.Core.Coercion
-- import GHC.Core.Coercion.Axiom
-- import CSlash.Core.FVs
import CSlash.Core.Type.Rep    -- needs to build types & coercions in a knot
-- import GHC.Core.TyCo.Subst ( substTyCoVars )
-- import GHC.Core.InstEnv
-- import GHC.Core.FamInstEnv
import CSlash.Core
-- import GHC.Core.RoughMap( RoughMatchTc(..) )
-- import CSlash.Core.Utils
-- import GHC.Core.Unfold( calcUnfoldingGuidance )
-- import GHC.Core.Unfold.Make
-- import GHC.Core.Lint
-- import GHC.Core.Make
-- import GHC.Core.Class
import CSlash.Core.TyCon
import CSlash.Core.ConLike
import CSlash.Core.DataCon
-- import GHC.Core.Opt.OccurAnal ( occurAnalyseExpr )
import CSlash.Core.Ppr

import CSlash.Unit.Env
import CSlash.Unit.External
import CSlash.Unit.Module
import CSlash.Unit.Module.ModDetails
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Home.ModInfo

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.Logger

import CSlash.Data.Bag
import CSlash.Data.Maybe
import CSlash.Data.FastString
import CSlash.Data.List.SetOps

-- import GHC.Types.Annotations
import CSlash.Types.SourceFile
import CSlash.Types.SourceText
import CSlash.Types.Basic hiding ( SuccessFlag(..) )
import CSlash.Types.CompleteMatch
import CSlash.Types.SrcLoc
import CSlash.Types.TypeEnv
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.DSet ( mkUniqDSet )
import CSlash.Types.Unique.Set ( nonDetEltsUniqSet )
import CSlash.Types.Unique.Supply
-- import CSlash.Types.Demand( isDeadEndSig )
import CSlash.Types.Literal
import CSlash.Types.Var as Var
import CSlash.Types.Var.Set
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Id
import CSlash.Types.Id.Make
import CSlash.Types.Id.Info
import CSlash.Types.Tickish
import CSlash.Types.TyThing
import CSlash.Types.Error

import CSlash.Utils.Fingerprint
-- import qualified GHC.Data.BooleanFormula as BF

import Control.Monad
import CSlash.Parser.Annotation
import CSlash.Driver.Env.KnotVars
-- import GHC.Unit.Module.WholeCoreBindings
import Data.IORef
import Data.Foldable
import CSlash.Builtin.Names ({-ioTyConName,-} rOOT_MAIN)
import CSlash.Iface.Errors.Types
import CSlash.Language.Syntax.Extension (NoExtField (NoExtField))

{- *********************************************************************
*                                                                      *
                Type declarations
*                                                                      *
********************************************************************* -}

-- tcIfaceDecl :: Bool -> IfaceDecl -> IfL TyThing
-- tcIfaceDecl = tc_iface_decl

-- tc_face_decl :: Bool -> IfaceDecl -> IfL TyThing
-- tc_face_decl ignore_prags (IfaceId { ifName = name, ifType = iface_type
--                                    , ifIdDetails = details, ifIdInfo = info }) = do
--   ty <- tcIfaceType iface_type
--   details <- tcIdDetails name ty details
--   info <- tcIdInfo ignore_prags TopLevel name ty info
--   return (AnId (mkGlobalId details name ty info))

-- tc_iface_decl _ (IfaceData { ifName = tc_name, ifBinders = binders
--                            , ifResKind = res_kind, ifCons = rdr_cons }) = do
--   panic "tc_iface_decl IfaceData"

-- tc_iface_decl _ (IfaceSynonym { ifName = tc_name, ifSynRhs = rhs_ty
--                               , ifBinders = binders, ifResKind = res_kind }) = do
--   panic "tc_iface_decl IfaceSynonym"

tcIfaceDecls :: Bool -> [(Fingerprint, IfaceDecl)] -> IfL [(Name, TyThing)]

-- remove empty case later later:
tcIfaceDecls _ [] = return []

tcIfaceDecls ignore_prags ver_decls = panic "tcIfaceDecls"
  -- = concatMapM (tc_iface_decl_fingerprint ignore_prags) ver_decls

-- tc_iface_decl_fingerprint :: Bool -> (FingerPrint, IfaceDecl) -> IfL [(Name, TyThing)]
-- tc_iface_decl_fingerprint ignore_prags (_, decl) = do
--   let main_name = ifName decl
--       doc = text "Declaration for" <+> ppr (ifName decl)
--   thing <- forkM doc $ do
--     bumpDeclStats main_name
--     tcIfaceDecl ignore_prags decl

--   let mini_env = mkOccEnv [(getOccName t, t) | t <- implicitTyThings thing]
--       lookup n = case lookupOccEnv mini_env (getOccName n) of
--                    Just thing -> thing
--                    Nothing -> pprPanic "tc_iface_decl_fingerprint"
--                               (ppr main_name <+> ppr n $$ ppr decl)
--   implicit_names <- mapM lookupIfaceTop (ifaceDeclImplicitBndrs decl)
--   return $ (main_name, thing)
--          : [(n, lookup n) | n <- implicit_names]

{- *********************************************************************
*                                                                      *
                Complete Match Pragmas
*                                                                      *
********************************************************************* -}

tcIfaceCompleteMatches :: [IfaceCompleteMatch] -> IfL [CompleteMatch]

-- remove empty case later
tcIfaceCompleteMatches [] = return []

tcIfaceCompleteMatches _ = panic "tcIfaceCompleteMatches"
