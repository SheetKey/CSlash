{-# LANGUAGE LambdaCase #-}
module CSlash.Rename.Names where

import CSlash.Driver.Env
import CSlash.Driver.Session
import CSlash.Driver.Ppr

import CSlash.Rename.Env
import CSlash.Rename.Fixity
import CSlash.Rename.Utils ( warnUnusedTopBinds )
import CSlash.Rename.Unbound as Unbound

import CSlash.Tc.Errors.Types
-- import GHC.Tc.Utils.Env
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Types.LclEnv
import CSlash.Tc.Zonk.TcType ( tcInitTidyEnv )

import CSlash.Cs
import CSlash.Iface.Load   ( loadSrcInterface )
import CSlash.Iface.Syntax ( fromIfaceWarnings )
import CSlash.Builtin.Names
-- import CSlash.Parser.PostProcess ( setRdrNameSpace )
import CSlash.Core.Type
import CSlash.Core.Type.Tidy
-- import GHC.Core.PatSyn
import CSlash.Core.TyCon ( TyCon, tyConName )
-- import qualified GHC.LanguageExtensions as LangExt

import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Misc as Utils
import CSlash.Utils.Panic

import CSlash.Types.Fixity.Env
-- import GHC.Types.SafeHaskell
import CSlash.Types.Name hiding (varName)
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
import CSlash.Types.Var.Id
import CSlash.Types.Var
import CSlash.Types.PcInfo
import CSlash.Types.PkgQual
import CSlash.Types.GREInfo (ConInfo(..), GREInfo(..))

import CSlash.Unit hiding (comparing)
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
  tcg_env <- getGblEnv
  let this_mod = tcg_mod tcg_env
  stuff <- mapAndReportM (rnImportDecl this_mod) imports
  return $ combine stuff

  where
    combine :: [(LImportDecl Rn, GlobalRdrEnv, ImportAvails, AnyPcUsage)]
            -> ([LImportDecl Rn], GlobalRdrEnv, ImportAvails, AnyPcUsage)
    combine = foldr plus ([], emptyGlobalRdrEnv, emptyImportAvails, False)

    plus (decl, gbl_env1, imp_avails1, pc_usage1)
         (decls, gbl_env2, imp_avails2, pc_usage2)
      = ( decl : decls
        , gbl_env1 `plusGlobalRdrEnv` gbl_env2
        , imp_avails1 `plusImportAvails` imp_avails2
        , pc_usage1 || pc_usage2 )
      
rnImportDecl
  :: Module
  -> (LImportDecl Ps, SDoc)
  -> RnM (LImportDecl Rn, GlobalRdrEnv, ImportAvails, AnyPcUsage)
rnImportDecl this_mod (L loc decl, import_reason) =
  let ImportDecl { ideclName = loc_imp_mod_name
                 , ideclPkgQual = raw_pkg_qual
                 , ideclQualified = qual_style
                 , ideclExt = XImportDeclPass { ideclImplicit = implicit }
                 , ideclAs = as_mod
                 , ideclImportList = imp_details } = decl
  in setSrcSpanA loc $ do
    let qual_only = isImportDeclQualified qual_style
        imp_mod_name = unLoc loc_imp_mod_name
        doc = ppr imp_mod_name <+> import_reason

    cs_env <- getTopEnv
    unit_env <- cs_unit_env <$> getTopEnv
    let pkg_qual = renameRawPkgQual unit_env imp_mod_name raw_pkg_qual

    when (imp_mod_name == moduleName this_mod
          && (case pkg_qual of
                NoPkgQual -> True
                ThisPkg uid -> uid == homeUnitId_ (cs_dflags cs_env)
                OtherPkg _ -> False))
      $ addErr (TcRnSelfImport imp_mod_name)

    case imp_details of
      Just (Exactly, _) -> return ()
      _ | implicit -> return ()
        | qual_only -> return ()
        | otherwise -> addDiagnostic (TcRnNoExplicitImportList imp_mod_name)

    iface <- loadSrcInterface doc imp_mod_name pkg_qual

    let imp_mod = mi_module iface
        qual_mod_name = fmap unLoc as_mod `orElse` imp_mod_name
        imp_spec = ImpDeclSpec { is_mod = imp_mod, is_qual = qual_only
                               , is_dloc = locA loc, is_as = qual_mod_name }

    (new_imp_details, gres) <- filterImports cs_env iface imp_spec imp_details

    potential_gres <- mkGlobalRdrEnv . snd <$> filterImports cs_env iface imp_spec Nothing

    let gbl_env = mkGlobalRdrEnv gres

        is_hiding | Just (EverythingBut, _) <- imp_details = True
                  | otherwise = False

    cs_env <- getTopEnv
    let home_unit = cs_home_unit cs_env
        other_home_units = cs_all_home_unit_ids cs_env
        imv = ImportedModsVal
              { imv_name = qual_mod_name
              , imv_span = locA loc
              , imv_is_hiding = is_hiding
              , imv_all_exports = potential_gres
              , imv_qualified = qual_only }
        imports = calculateAvails home_unit other_home_units iface (ImportedByUser imv)

    -- case fromIfaceWarnings (mi_warns iface) of
    --   WarnAll txt -> addDiagnostic (TcRnDeprecatedModule imp_mod_name txt)
    --   _ -> return ()

    let new_imp_decl = ImportDecl
          { ideclExt = ideclExt decl
          , ideclName = ideclName decl
          , ideclPkgQual = pkg_qual
          , ideclQualified = ideclQualified decl
          , ideclAs = ideclAs decl
          , ideclImportList = new_imp_details }

    return (L loc new_imp_decl, gbl_env, imports, mi_pc iface)

renameRawPkgQual :: UnitEnv -> ModuleName -> RawPkgQual -> PkgQual
renameRawPkgQual _ _ NoRawPkgQual = NoPkgQual
renameRawPkgQual _ _ (RawPkgQual _) = panic "renameRawPkgQual RawPkgQual"

calculateAvails
  :: HomeUnit
  -> S.Set UnitId
  -> ModIface
  -> ImportedBy
  -> ImportAvails
calculateAvails home_unit other_home_units iface imported_by =
  let imp_mod = mi_module iface
      imp_sem_mod = mi_semantic_module iface
      deps = mi_deps iface

      pkg = moduleUnit (mi_module iface)
      ipkg = toUnitId pkg

      dependent_pkgs = if ipkg `S.member` other_home_units
                       then S.empty
                       else S.singleton ipkg

      direct_mods = mkModDeps $ if ipkg `S.member` other_home_units
                                then S.singleton (moduleUnitId imp_mod, moduleName imp_mod)
                                else S.empty
  in ImportAvails
     { imp_mods = unitModuleEnv (mi_module iface) [imported_by]
     , imp_direct_dep_mods = direct_mods
     , imp_dep_direct_pkgs = dependent_pkgs
     }

{- *********************************************************************
*                                                                      *
            importsFromLocalDecls
*                                                                      *
********************************************************************* -}

extendGlobalRdrEnvRn :: [GlobalRdrElt] -> MiniFixityEnv -> RnM (TcGblEnv Tc, TcLclEnv)
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

getLocalNonValBinders :: MiniFixityEnv -> CsGroup Ps -> RnM ((TcGblEnv Tc, TcLclEnv), NameSet)
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
      let tc_gre = mkLocalTyConGRE tc_flav tycon_name
      traceRn "getLocalNonValBinders new_tc" $
        vcat [ text "tycon:" <+> ppr tycon_name
             , text "tc_gre:" <+> ppr tc_gre ]
      return $ [tc_gre]

{- *********************************************************************
*                                                                      *
        Filtering imports
*                                                                      *
********************************************************************* -}

gresFromAvail :: HasDebugCallStack => CsEnv -> Maybe ImportSpec -> AvailInfo -> [GlobalRdrElt]
gresFromAvail cs_env prov avail =
  [ mk_gre nm info
  | nm <- availNames avail
  , let info = lookupGREInfo cs_env nm ]
  where
    mk_gre n info = case prov of
      Nothing -> GRE { gre_name = n, gre_par = mkParent n avail
                     , gre_lcl = True, gre_imp = emptyBag
                     , gre_info = info }
      Just is -> GRE { gre_name = n, gre_par = mkParent n avail
                     , gre_lcl = False, gre_imp = unitBag is
                     , gre_info = info }

gresFromAvails :: CsEnv -> Maybe ImportSpec -> [AvailInfo] -> [GlobalRdrElt]
gresFromAvails cs_env prov = concatMap (gresFromAvail cs_env prov)

filterImports
  :: HasDebugCallStack
  => CsEnv
  -> ModIface
  -> ImpDeclSpec
  -> Maybe (ImportListInterpretation, LocatedL [LIE Ps])
  -> RnM (Maybe (ImportListInterpretation, LocatedL [LIE Rn]), [GlobalRdrElt])
filterImports cs_env iface decl_spec Nothing
  = return (Nothing, gresFromAvails cs_env (Just imp_spec) all_avails)
  where
    all_avails = mi_exports iface
    imp_spec = ImpSpec { is_decl = decl_spec, is_item = ImpAll }
filterImports cs_env iface decl_spec (Just (want_hiding, L l import_items)) = do
  items1 <- mapM lookup_lie import_items

  let items2 = concat items1

      gres = case want_hiding of
        Exactly -> concatMap (gresFromIE decl_spec) items2
        EverythingBut ->
          let hidden_names = mkNameSet $ concatMap (map greName . snd) items2
              keep n = not (n `elemNameSet` hidden_names)
              all_gres = gresFromAvails cs_env (Just hiding_spec) all_avails
          in filter (keep . greName) all_gres
  return (Just (want_hiding, L l (map fst items2)), gres)

  where
    import_mod = mi_module iface
    all_avails = mi_exports iface
    hiding_spec = ImpSpec { is_decl = decl_spec, is_item = ImpAll }
    imp_occ_env = mkImportOccEnv cs_env decl_spec all_avails

    lookup_parent :: IE Ps -> RdrName -> IELookupM ImpOccItem
    lookup_parent ie rdr =
      assertPpr (not $ isVarNameSpace ns)
        (vcat [ text "filterImports lookup_parent: unexpected variable"
              , text "rdr:" <+> ppr rdr
              , text "namespace:" <+> pprNameSpace ns ]) $ 
      do xs <- lookup_names ie rdr
         case xs of
           cax :| [] -> return cax
           _ -> pprPanic "filter_imports lookup_parent ambiguous" $
                vcat [ text "rdr:" <+> ppr rdr
                     , text "lookups:" <+> ppr (fmap imp_item xs) ]
      where
        occ = rdrNameOcc rdr
        ns = occNameSpace occ

    lookup_names :: IE Ps -> RdrName -> IELookupM (NonEmpty ImpOccItem)
    lookup_names ie rdr
      | isQual rdr
      = failLookupWith (QualImportError rdr)
      | otherwise
      = case lookups of
          [] -> failLookupWith (BadImport ie IsNotSubordinate)
          item:items -> return $ item :| items
      where
        lookups = concatMap nonDetNameEnvElts $
                  lookupImpOccEnv (RelevantGREs False) imp_occ_env (rdrNameOcc rdr)

    lookup_lie :: LIE Ps -> TcRn [(LIE Rn, [GlobalRdrElt])]
    lookup_lie (L loc ieRdr) = setSrcSpanA loc $ do
      (stuff, warns) <- liftM (fromMaybe ([], [])) $ run_lookup (lookup_ie ieRdr)
      mapM_ (addTcRnDiagnostic <=< warning_msg) warns
      return [ (L loc ie, gres) | (ie, gres) <- stuff ]

      where
        warning_msg (DodgyImport n) = pure $ TcRnDodgyImports (DodgyImportsEmptyParent n)
        warning_msg MissingImportList = pure $ TcRnMissingImportList ieRdr
        warning_msg (BadImportW ie) = do
          reason <- badImportItemErr iface decl_spec ie IsNotSubordinate all_avails
          pure $ TcRnDodgyImports (DodgyImportsHiding reason)

        run_lookup :: IELookupM a -> TcRn (Maybe a)
        run_lookup m = case m of
          Failed err -> do msg <- lookup_err_msg err
                           addErr $ TcRnImportLookup msg
                           return Nothing
          Succeeded a -> return $ Just a

        lookup_err_msg err = case err of
          BadImport ie sub -> badImportItemErr iface decl_spec ie sub all_avails
          IllegalImport -> pure ImportLookupIllegal
          QualImportError rdr -> pure $ ImportLookupQualified rdr

    lookup_ie :: IE Ps -> IELookupM ([(IE Rn, [GlobalRdrElt])], [IELookupWarning])
    lookup_ie ie = handle_bad_import $ case ie of
      IEVar _ (L l n) -> do
        xs <- lookup_names ie (ieWrappedName n)
        let gres = map imp_item $ NE.toList xs
        return ( [ (IEVar noExtField (L l (replaceWrappedName n name)), [gre])
                 | gre <- gres
                 , let name = greName gre ]
               , [] )
      _ -> failLookupWith IllegalImport

      where
        handle_bad_import m = catchIELookup m $ \err -> case err of
          BadImport ie _
            | want_hiding == EverythingBut
              -> return ([], [BadImportW ie])
          _ -> failLookupWith err

type IELookupM = MaybeErr IELookupError

data IELookupWarning
  = BadImportW (IE Ps)
  | MissingImportList
  | DodgyImport GlobalRdrElt

data IsSubordinate = IsSubordinate | IsNotSubordinate

data IELookupError
  = QualImportError RdrName
  | BadImport (IE Ps) IsSubordinate
  | IllegalImport

failLookupWith :: IELookupError -> IELookupM a
failLookupWith err = Failed err

catchIELookup :: IELookupM a -> (IELookupError -> IELookupM a) -> IELookupM a
catchIELookup m h = case m of
  Succeeded r -> return r
  Failed err -> h err

data ImpOccItem = ImpOccItem
  { imp_item :: GlobalRdrElt
  , imp_bundled :: [GlobalRdrElt]
  , imp_is_parent :: Bool
  }

instance Outputable ImpOccItem where
  ppr (ImpOccItem { imp_item = item, imp_bundled = bundled, imp_is_parent = is_par })
    = braces $ hsep
      [ text "ImpOccItem"
      , if is_par then text "[is_par]" else empty
      , ppr (greName item) <+> ppr (greParent item)
      , braces $ text "bundled:" <+> ppr (map greName bundled) ]

mkImportOccEnv :: CsEnv -> ImpDeclSpec -> [IfaceExport] -> OccEnv (NameEnv ImpOccItem)
mkImportOccEnv cs_env decl_spec all_avails =
  mkOccEnv_C (plusNameEnv_C combine)
  [ (occ, mkNameEnv [(nm, item)])
  | avail <- all_avails
  , let gres = gresFromAvail cs_env (Just hiding_spec) avail
  , gre <- gres
  , let nm = greName gre
        occ = greOccName gre
        (is_parent, bundled) = case avail of
          AvailTC c _
            | c == nm -> (True, drop 1 gres)
            | otherwise -> (False, gres)
          _ -> (False, [])
        item = ImpOccItem { imp_item = gre, imp_bundled = bundled, imp_is_parent = is_parent } ]
  where
    hiding_spec = ImpSpec { is_decl = decl_spec, is_item = ImpAll }

    combine :: ImpOccItem -> ImpOccItem -> ImpOccItem
    combine item1@(ImpOccItem { imp_item = gre1, imp_is_parent = is_parent1 })
            item2@(ImpOccItem { imp_item = gre2, imp_is_parent = is_parent2 })
      | is_parent1 || is_parent2
      , let name1 = greName gre1
            name2 = greName gre2
            gre = gre1 `plusGRE` gre2
      = assertPpr (name1 == name2) (ppr name1 <+> ppr name2) $
        if is_parent1
        then item1 { imp_item = gre }
        else item2 { imp_item = gre }
    combine item1@(ImpOccItem { imp_item = c1, imp_bundled = kids1 })
            item2@(ImpOccItem { imp_item = c2, imp_bundled = kids2 })
      = assertPpr (greName c1 == greName c2
                   && (not (null kids1 && null kids2)))
                  (ppr c1 <+> ppr c2 <+> ppr kids1 <+> ppr kids2) $
        if null kids1 then item2 else item1

lookupImpOccEnv
  :: WhichGREs GREInfo -> OccEnv (NameEnv ImpOccItem) -> OccName -> [NameEnv ImpOccItem]
lookupImpOccEnv which_gres env occ =
  mapMaybe relevant_items $ lookupOccEnv_AllNameSpaces env occ
  where
    is_relevant :: ImpOccItem -> Bool
    is_relevant (ImpOccItem { imp_item = gre }) =
      greIsRelevant which_gres (occNameSpace occ) gre

    relevant_items :: NameEnv ImpOccItem -> Maybe (NameEnv ImpOccItem)
    relevant_items nms =
      let nms' = filterNameEnv is_relevant nms
      in if isEmptyNameEnv nms' then Nothing else Just nms'

{- *********************************************************************
*                                                                      *
            Import/Export utils
*                                                                      *
********************************************************************* -}

gresFromIE :: ImpDeclSpec -> (LIE Rn, [GlobalRdrElt]) -> [GlobalRdrElt]
gresFromIE decl_spec (L loc ie, gres) = map set_gre_imp gres
  where
    is_explicit = case ie of
                    -- IEThingAll _ name _ -> \n -> n == lieWrappedName name
                    _ -> const True
    prov_fn name = ImpSpec { is_decl = decl_spec, is_item = item_spec }
      where item_spec = ImpSome { is_explicit = is_explicit name
                                , is_iloc = locA loc }
    set_gre_imp gre@(GRE { gre_name = nm })
      = gre { gre_imp = unitBag $ prov_fn nm }

mkChildEnv :: [GlobalRdrElt] -> NameEnv [GlobalRdrElt]
mkChildEnv gres = foldr add emptyNameEnv gres
  where
    add gre env = case greParent gre of
      ParentIs p -> extendNameEnv_Acc (:) Utils.singleton env p gre
      NoParent -> env

findChildren :: NameEnv [a] -> Name -> [a]
findChildren env n = lookupNameEnv env n `orElse` []


{- *********************************************************************
*                                                                      *
            Unused names
*                                                                      *
********************************************************************* -}

reportUnusedNames :: TcGblEnv Zk -> CsSource -> ZkM ()
reportUnusedNames gbl_env cs_src = do
  keep <- readTcRef (tcg_keep gbl_env)
  traceRn "RUN" (ppr (tcg_dus gbl_env))
  warnUnusedImportDecls gbl_env cs_src
  warnUnusedTopBinds $ unused_locals keep
  warnMissingSignatures gbl_env
  where
    used_names keep = findUses (tcg_dus gbl_env) emptyNameSet `unionNameSet` keep

    defined_names = globalRdrEnvElts (tcg_rdr_env gbl_env)

    kids_env = mkChildEnv defined_names

    gre_is_used used_names gre0 = name `elemNameSet` used_names
                                  || any (\gre -> greName gre `elemNameSet` used_names)
                                         (findChildren kids_env name)
      where
        name = greName gre0

    unused_locals keep
      = let (_, defined_but_not_used) = partition (gre_is_used (used_names keep)) defined_names
        in filter is_unused_local defined_but_not_used

    is_unused_local gre = isLocalGRE gre && isExternalName (greName gre)

{- *********************************************************************
*                                                                      *
            Missing signatures
*                                                                      *
********************************************************************* -}
 
warnMissingSignatures :: TcGblEnv Zk -> ZkM ()
warnMissingSignatures gbl_env = do
  let exports = availsToNameSet (tcg_exports gbl_env)
      sig_ns = tcg_sigs gbl_env

      binds = collectCsBindsBinders CollNoDictBinders $ tcg_binds gbl_env

      not_generated name = name `elemNameSet` sig_ns

      add_binding_warn :: Id Zk -> ZkM ()
      add_binding_warn id = when (not_generated name) $ do
        env <- liftZonkM $ tcInitTidyEnv
        let ty = tidyOpenType env (panic "varType id")
            missing = panic "MissingTopLevelBindingSig name ty"
            diag = TcRnMissingSignature missing exported
        addDiagnosticAt (getSrcSpan name) diag
        where
          name = varName id
          exported = if name `elemNameSet` exports then IsExported else IsNotExported

  mapM_ add_binding_warn binds

{- *********************************************************************
*                                                                      *
            Unused imports
*                                                                      *
********************************************************************* -}

type ImportDeclUsage = (LImportDecl Rn, [GlobalRdrElt], [Name])

warnUnusedImportDecls :: TcGblEnv Zk -> CsSource -> ZkM ()
warnUnusedImportDecls gbl_env cs_src = do
  uses <- readMutVar (tcg_used_gres gbl_env)
  let user_imports = filterOut (ideclImplicit . ideclExt . unLoc) (tcg_rn_imports gbl_env)

      rdr_env = tcg_rdr_env gbl_env

      usage = findImportUsage user_imports uses

  traceRn "warnUnusedImportDecls"
    $ vcat [ text "Uses:" <+> ppr uses
           , text "Import usage" <+> ppr usage ]

  mapM_ (warnUnusedImport rdr_env) usage

  whenGOptM Opt_D_dump_minimal_imports
    $ panic "printMinimalImports cs_src usage"

findImportUsage :: [LImportDecl Rn] -> [GlobalRdrElt] -> [ImportDeclUsage]
findImportUsage imports used_gres = map unused_decl imports
  where
    import_usage = mkImportMap used_gres

    unused_decl decl@(L loc (ImportDecl { ideclImportList = imps }))
      = (decl, used_gres, nameSetElemsStable unused_imps)
      where
        used_gres = lookupSrcLoc (srcSpanEnd $ locA loc) import_usage
                    `orElse` []

        used_name = mkNameSet (map greName used_gres)
        used_parents = mkNameSet (mapMaybe greParent_maybe used_gres)

        unused_imps = case imps of
          Just (Exactly, L _ imp_ies) -> foldr (add_unused . unLoc) emptyNameSet imp_ies
          _ -> emptyNameSet

        add_unused (IEVar _ n) acc = add_unused_name (lieWrappedName n) acc
        add_unused (IEModuleContents{}) acc = acc

        add_unused_name n acc
          | n `elemNameSet` used_name = acc
          | otherwise = acc `extendNameSet` n

type ImportMap = Map RealSrcLoc [GlobalRdrElt]

mkImportMap :: [GlobalRdrElt] -> ImportMap
mkImportMap gres = foldr add_one Map.empty gres
  where
    add_one gre@(GRE { gre_imp = imp_specs }) imp_map
      = case srcSpanEnd (is_dloc (is_decl best_imp_spec)) of
          RealSrcLoc decl_loc _ -> Map.insertWith add decl_loc [gre] imp_map
          UnhelpfulLoc _ -> imp_map
          where
            best_imp_spec = case bagToList imp_specs of
                              [] -> pprPanic "mkImportPat: GRE with no ImportSpecs" (ppr gre)
                              is:iss -> bestImport (is NE.:| iss)
            add _ gres = gre : gres

warnUnusedImport :: GlobalRdrEnv -> ImportDeclUsage -> TcRnZk p ()
warnUnusedImport rdr_env (L loc decl, used, unused)
  | Just (Exactly, L _ []) <- ideclImportList decl
  = return ()

  | null used
  = addDiagnosticAt (locA loc) (TcRnUnusedImport decl UnusedImportNone)

  | null unused
  = return ()

  | Just (_, L _ imports) <- ideclImportList decl
  , length unused == 1
  , Just (L loc _) <- find (\(L _ ie) -> ((ieName ie) :: Name) `elem` unused) imports
  = addDiagnosticAt (locA loc) (TcRnUnusedImport decl (UnusedImportSome sort_unused))

  | otherwise
  = addDiagnosticAt (locA loc) (TcRnUnusedImport decl (UnusedImportSome sort_unused))

  where
    sort_unused = UnusedImportNameRegular <$> sortBy (comparing nameOccName) unused

{- *********************************************************************
*                                                                      *
            Errors
*                                                                      *
********************************************************************* -}

badImportItemErr
  :: ModIface
  -> ImpDeclSpec
  -> IE Ps
  -> IsSubordinate
  -> [AvailInfo]
  -> TcRn ImportLookupReason
badImportItemErr iface decl_spec ie sub avails = do
  dflags <- getDynFlags
  cs_env <- getTopEnv
  let rdr_env = mkGlobalRdrEnv $ gresFromAvails cs_env (Just imp_spec) all_avails
  pure $ ImportLookupBad (importErrorKind dflags rdr_env) iface decl_spec ie
  where
    importErrorKind dflags rdr_env
      | any checkIfTyCon avails = case sub of
          IsNotSubordinate -> BadImportAvailTyCon
          IsSubordinate -> BadImportNotExportedSubordinates unavailableChildren
      | any checkIfVarName avails = BadImportAvailVar
      | Just con <- find checkIfDataCon avails = BadImportAvailDataCon $ availOccName con
      | otherwise = BadImportNotExported suggs
        where
          suggs = similar_suggs
          similar_names = similarNameSuggestions (Unbound.LF WL_Anything WL_Global)
                                                 dflags rdr_env emptyLocalRdrEnv rdr
          similar_suggs = case NE.nonEmpty $ mapMaybe imported_item $ similar_names of
            Just similar -> [ SuggestSimilarNames rdr similar ]
            Nothing -> []
          imported_item (SimilarRdrName rdr_name (Just (ImportedBy {})))
            = Just (SimilarRdrName rdr_name Nothing)
          imported_item _ = Nothing

    checkIfDataCon = checkIfAvailMatches isDataConName
    checkIfTyCon = checkIfAvailMatches isTyConName
    checkIfVarName = \case
      AvailTC{} -> False
      Avail n -> importedFS == occNameFS (occName n)
                  && isVarOcc (occName n)
    checkIfAvailMatches namePred = \case
      AvailTC _ ns -> case find (\n -> importedFS == occNameFS (occName n)) ns of
                        Just n -> namePred n
                        Nothing -> False
      Avail {} -> False
    availOccName = occName . availName
    rdr = ieName ie
    importedFS = occNameFS $ rdrNameOcc rdr
    imp_spec = ImpSpec { is_decl = decl_spec, is_item = ImpAll }
    all_avails = mi_exports iface
    unavailableChildren = case ie of
      --IEThingWith _ _ _ ns _ -> map (rdrNameOcc . ieWrappedName . unLoc) ns
      _ -> panic "importedChildren failed patten match: no children"

addDupDeclErr :: NonEmpty GlobalRdrElt -> TcRn ()
addDupDeclErr gres@(gre :| _)
  = addErrAt (getSrcSpan (NE.last sorted_names))
    $ (TcRnDuplicateDecls (greOccName gre) sorted_names)
  where
    sorted_names = NE.sortBy (SrcLoc.leftmost_smallest `on` nameSrcSpan) (fmap greName gres)
