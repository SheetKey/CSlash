module CSlash.Rename.Names where

import CSlash.Driver.Env
import CSlash.Driver.Session
import CSlash.Driver.Ppr

import CSlash.Rename.Env
import CSlash.Rename.Fixity
-- import GHC.Rename.Utils ( warnUnusedTopBinds )
-- import GHC.Rename.Unbound
-- import qualified GHC.Rename.Unbound as Unbound

import CSlash.Tc.Errors.Types
-- import GHC.Tc.Utils.Env
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Types.LclEnv
-- import GHC.Tc.Zonk.TcType ( tcInitTidyEnv )

import CSlash.Cs
-- import CSlash.Iface.Load   ( loadSrcInterface )
-- import CSlash.Iface.Syntax ( fromIfaceWarnings )
import CSlash.Builtin.Names
-- import CSlash.Parser.PostProcess ( setRdrNameSpace )
import CSlash.Core.Type
-- import GHC.Core.PatSyn
import CSlash.Core.TyCon ( TyCon, tyConName )
-- import qualified GHC.LanguageExtensions as LangExt

import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Misc as Utils
import CSlash.Utils.Panic

import CSlash.Types.Fixity.Env
-- import GHC.Types.SafeHaskell
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set
import CSlash.Types.Name.Reader
import CSlash.Types.Avail
-- import GHC.Types.FieldLabel
import CSlash.Types.Hint
import CSlash.Types.SourceFile
import CSlash.Types.SrcLoc as SrcLoc
import CSlash.Types.Basic  ( TopLevelFlag(..) )
import CSlash.Types.SourceText
import CSlash.Types.Id
import CSlash.Types.PcInfo
import CSlash.Types.PkgQual
import CSlash.Types.GREInfo (ConInfo(..))

import CSlash.Unit
import CSlash.Unit.Module.Warnings
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.Imported
import CSlash.Unit.Module.Deps
import CSlash.Unit.Env

import CSlash.Data.Bag
import CSlash.Data.FastString
import CSlash.Data.FastString.Env
import CSlash.Data.Maybe
import CSlash.Data.List.SetOps ( removeDups )

import Control.Monad
import Data.Foldable    ( for_ )
import Data.IntMap      ( IntMap )
import qualified Data.IntMap as IntMap
import Data.Map         ( Map )
import qualified Data.Map as Map
import Data.Ord         ( comparing )
import Data.List        ( partition, find, sortBy )
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Function    ( on )
import qualified Data.Set as S
import System.FilePath  ((</>))
import System.IO

{- *********************************************************************
*                                                                      *
            rnImports
*                                                                      *
********************************************************************* -}

rnImports
  :: [(LImportDecl Ps, SDoc)] -> RnM ([LImportDecl Rn], GlobalRdrEnv, ImportAvails, AnyPcUsage)
rnImports imports = do
  panic "rnImports"

renameRawPkgQual :: UnitEnv -> ModuleName -> RawPkgQual -> PkgQual
renameRawPkgQual _ _ NoRawPkgQual = NoPkgQual
renameRawPkgQual _ _ (RawPkgQual _) = panic "renameRawPkgQual RawPkgQual"

{- *********************************************************************
*                                                                      *
            importsFromLocalDecls
*                                                                      *
********************************************************************* -}

extendGlobalRdrEnvRn :: [GlobalRdrElt] -> MiniFixityEnv -> RnM (TcGblEnv, TcLclEnv)
extendGlobalRdrEnvRn new_gres new_fixities = checkNoErrs $ do
  (gbl_env, lcl_env) <- getEnvs
  let rdr_env1 = tcg_rdr_env gbl_env
      fix_env1 = tcg_fix_env gbl_env
  rdr_env2 <- foldlM add_gre rdr_env1 new_gres
  let fix_env2 = foldl' extend_fix_env fix_env1 new_gres
      gbl_env' = gbl_env { tcg_rdr_env = rdr_env2, tcg_fix_env = fix_env2 }
  traceRn "extendGlobalRdrEnvRn 2" (pprGlobalRdrEnv True rdr_env2)
  return (gbl_env', lcl_env)
  where
    extend_fix_env fix_env gre
      | Just (L _ fi) <- lookupMiniFixityEnv new_fixities name
      = extendNameEnv fix_env name (FixItem occ fi)
      | otherwise
      = fix_env
      where
        name = greName gre
        occ = greOccName gre

    add_gre :: GlobalRdrEnv -> GlobalRdrElt -> RnM GlobalRdrEnv
    add_gre env gre
      | not (null dups)
      = do addDupDeclErr (gre :| dups)
           return env
      | otherwise
      = return $ extendGlobalRdrEnv env gre
      where
        dups = filter isBadDupGRE
          $ lookupGRE env (LookupOccName (greOccName gre) (RelevantGREs False))
        isBadDupGRE old_gre = isLocalGRE old_gre && greClashesWith gre old_gre

{- *********************************************************************
*                                                                      *
    getLocalDeclBindersd@ returns the names for an CsDecl
             It's used for source code.
*                                                                      *
********************************************************************* -}

getLocalNonValBinders :: MiniFixityEnv -> CsGroup Ps -> RnM ((TcGblEnv, TcLclEnv), NameSet)
getLocalNonValBinders fixity_env CsGroup{ cs_valds = binds, cs_typeds = type_decls } = do
  tc_gres <- concatMapM new_tc (typeGroupTypeDecls type_decls)
  traceRn "getLocalNonValBinders 1" (ppr tc_gres)
  envs <- extendGlobalRdrEnvRn tc_gres fixity_env
  restoreEnvs envs $ do
    let new_bndrs = gresToNameSet tc_gres
    traceRn "getLocalNonValBinders 2" (Outputable.empty)
    envs <- extendGlobalRdrEnvRn [] fixity_env
    return (envs, new_bndrs)

  where
    new_tc :: LCsBind Ps -> RnM [GlobalRdrElt]
    new_tc tc_decl = do
      let TyDeclBinders (main_bndr, tc_flav) = csLTyDeclBinders tc_decl
      tycon_name <- newTopSrcBinder $ la2la main_bndr
      let tc_gre = mkLocalTyConGRE (fmap (const tycon_name) tc_flav) tycon_name
      traceRn "getLocalNonValBinders new_tc" $
        vcat [ text "tycon:" <+> ppr tycon_name
             , text "tc_gre:" <+> ppr tc_gre ]
      return $ [tc_gre]

{- *********************************************************************
*                                                                      *
            Unused names
*                                                                      *
********************************************************************* -}

reportUnusedNames :: TcGblEnv -> CsSource -> RnM ()
reportUnusedNames gbl_env cs_src = do
  panic "reportUnusedNames"

{- *********************************************************************
*                                                                      *
            Missing signatures
*                                                                      *
********************************************************************* -}



{- *********************************************************************
*                                                                      *
            Unused imports
*                                                                      *
********************************************************************* -}

{- *********************************************************************
*                                                                      *
            Errors
*                                                                      *
********************************************************************* -}

addDupDeclErr :: NonEmpty GlobalRdrElt -> TcRn ()
addDupDeclErr gres@(gre :| _)
  = addErrAt (getSrcSpan (NE.last sorted_names))
    $ (TcRnDuplicateDecls (greOccName gre) sorted_names)
  where
    sorted_names = NE.sortBy (SrcLoc.leftmost_smallest `on` nameSrcSpan) (fmap greName gres)
