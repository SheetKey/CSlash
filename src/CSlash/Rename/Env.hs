module CSlash.Rename.Env where

import CSlash.Iface.Load
import CSlash.Iface.Env
import CSlash.Cs
import CSlash.Types.Name.Reader
import CSlash.Tc.Errors.Types
import CSlash.Tc.Errors.Ppr (pprScopeError)
-- import CSlash.Tc.Utils.Env
import CSlash.Tc.Types.LclEnv
import CSlash.Tc.Utils.Monad
-- import CSlash.Parser.PostProcess ( setRdrNameSpace )
import CSlash.Builtin.Types
import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.Name.Env
import CSlash.Types.Avail
import CSlash.Types.Hint
import CSlash.Types.Error
import CSlash.Unit.Module
import CSlash.Unit.Module.ModIface
import CSlash.Core.ConLike
import CSlash.Core.DataCon
import CSlash.Core.TyCon
import CSlash.Builtin.Names( rOOT_MAIN )
import CSlash.Types.Basic  ( TopLevelFlag(..), TupleSort(..), tupleSortBoxity, TyConFlavor(..) )
import CSlash.Types.TyThing ( TyThing(..), tyThingGREInfo )
import CSlash.Types.SrcLoc as SrcLoc
import CSlash.Utils.Outputable as Outputable
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.Set
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Data.Maybe
import CSlash.Driver.Env
import CSlash.Driver.Session
import CSlash.Data.FastString
import CSlash.Data.List.SetOps ( minusList )
-- import qualified GHC.LanguageExtensions as LangExt
import CSlash.Rename.Unbound
import CSlash.Rename.Utils
import CSlash.Data.Bag
import CSlash.Types.PkgQual
import CSlash.Types.GREInfo

import Control.Arrow    ( first )
import Control.Monad
import Data.Either      ( partitionEithers )
import Data.Function    ( on )
import Data.List        ( find, partition, groupBy, sortBy )
import qualified Data.List.NonEmpty as NE
import qualified Data.Semigroup as Semi
import System.IO.Unsafe ( unsafePerformIO )

{- *****************************************************
*                                                      *
                Source-code binders
*                                                      *
***************************************************** -}

newTopSrcBinder :: LocatedN RdrName -> RnM Name
newTopSrcBinder (L loc rdr_name)
  | Just name <- isExact_maybe rdr_name
  = if isExternalName name
    then do this_mod <- getModule
            unless (this_mod == nameModule name) $
              addErrAt (locA loc) (TcRnBindingOfExistingName rdr_name)
            return name
    else do this_mod <- getModule
            externalizeName this_mod name
  | Just (rdr_mod, rdr_occ) <- isOrig_maybe rdr_name
  = do this_mod <- getModule
       unless (rdr_mod == this_mod || rdr_mod == rOOT_MAIN) $
         addErrAt (locA loc) (TcRnBindingOfExistingName rdr_name)
       newGlobalBinder rdr_mod rdr_occ (locA loc)
  | otherwise
  = do when (isQual rdr_name) $
         addErrAt (locA loc) (badQualBndrErr rdr_name)
       this_mod <- getModule
       traceRn "newTopSrcBinder" (ppr this_mod $$ ppr rdr_name $$ ppr (locA loc))
       newGlobalBinder this_mod (rdrNameOcc rdr_name) (locA loc)

{- *****************************************************
*                                                      *
        Source code occurrences
*                                                      *
***************************************************** -}

lookupTopBndrRn :: WhatLooking -> RdrName -> RnM Name
lookupTopBndrRn which_suggest rdr_name = lookupExactOrOrig rdr_name greName $ do
  let occ = rdrNameOcc rdr_name
  env <- getGlobalRdrEnv
  case filter isLocalGRE (lookupGRE env $ LookupRdrName rdr_name $ RelevantGREs False) of
    [gre] -> return (greName gre)
    _ -> do traceRn "lookupTopBndrRn fail" (ppr rdr_name)
            unboundName (LF which_suggest WL_LocalTop) rdr_name

lookupLocatedTopConstructorRnN :: LocatedN RdrName -> RnM (LocatedN Name)
lookupLocatedTopConstructorRnN = wrapLocMA (lookupTopBndrRn WL_Constructor)

lookupExactOcc_either :: Name -> RnM (Either NotInScopeError GlobalRdrElt)
lookupExactOcc_either name
  | Just thing <- wiredInNameTyThing_maybe name
  , Just tycon <- case thing of
                    ATyCon tc -> Just tc
                    AConLike (RealDataCon dc) -> Just (dataConTyCon dc)
                    _ -> Nothing
  , isTupleTyCon tycon
  = do let tupArity = tyConArity tycon
           info = case thing of
                    ATyCon {} -> IAmTyCon TupleFlavor
                    _ -> IAmConLike $ mkConInfo tupArity
       checkTupSize tupArity
       return $ Right $ mkExactGRE name info
  | isExternalName name
  = do info <- lookupExternalExactName name
       return $ Right $ mkExactGRE name info
  | otherwise
  = lookupLocalExactGRE name

lookupExternalExactName :: Name -> RnM GREInfo
lookupExternalExactName name = do
  thing <- case wiredInNameTyThing_maybe name of
             Just thing -> return thing
             _ -> panic "tcLookupGlobal name"
  return $ tyThingGREInfo thing

lookupLocalExactGRE :: Name -> RnM (Either NotInScopeError GlobalRdrElt)
lookupLocalExactGRE name = do
  env <- getGlobalRdrEnv
  let lk = LookupExactName { lookupExactName = name, lookInAllNameSpaces = True }
  case lookupGRE env lk of
    [gre] -> return $ Right gre
    [] -> do lcl_env <- getLocalRdrEnv
             let gre = mkLocalVanillaGRE NoParent name
             if name `inLocalRdrEnvScope` lcl_env
               then return $ Right gre
               else return $ Left $ NoExactName name
    gres -> return $ Left $ SameName gres

lookupExactOrOrig :: RdrName -> (GlobalRdrElt -> r) -> RnM r -> RnM r
lookupExactOrOrig rdr_name res k = do
  men <- lookupExactOrOrig_base rdr_name
  case men of
    FoundExactOrOrig gre -> return $ res gre
    NotExactOrOrig -> k
    ExactOrOrigError e -> do
      addErr (mkTcRnNotInScope rdr_name e)
      return $ res (mkUnboundGRERdr rdr_name)

lookupExactOrOrig_maybe :: RdrName -> (Maybe GlobalRdrElt -> r) -> RnM r -> RnM r
lookupExactOrOrig_maybe rdr_name res k = do
  men <- lookupExactOrOrig_base rdr_name
  case men of
    FoundExactOrOrig gre -> return (res (Just gre))
    ExactOrOrigError _ -> return (res Nothing)
    NotExactOrOrig -> k

data ExactOrOrigResult
  = FoundExactOrOrig GlobalRdrElt
  | ExactOrOrigError NotInScopeError
  | NotExactOrOrig

lookupExactOrOrig_base :: RdrName -> RnM ExactOrOrigResult
lookupExactOrOrig_base rdr_name
  | Just n <- isExact_maybe rdr_name
  = cvtEither <$> lookupExactOcc_either n
  | Just (rdr_mod, rdr_occ) <- isOrig_maybe rdr_name
  = do nm <- lookupOrig rdr_mod rdr_occ
       this_mod <- getModule
       mb_gre <- if nameIsLocalOrFrom this_mod nm
                 then lookupLocalExactGRE nm
                 else do info <- lookupExternalExactName nm
                         return $ Right $ mkExactGRE nm info
       return $ cvtEither mb_gre
  | otherwise = return NotExactOrOrig
  where
    cvtEither (Left e) = ExactOrOrigError e
    cvtEither (Right gre) = FoundExactOrOrig gre

lookupLocalOccRn_maybe :: RdrName -> RnM (Maybe Name)
lookupLocalOccRn_maybe rdr_name = do
  local_env <- getLocalRdrEnv
  return $ lookupLocalRdrEnv local_env rdr_name

lookupTypeOccRn :: RdrName -> RnM Name
lookupTypeOccRn rdr_name = do
  mb_gre <- lookupOccRn_maybe rdr_name
  case mb_gre of
    Just gre -> return $ greName gre
    Nothing -> unboundName (LF WL_Anything WL_Anywhere) rdr_name

lookupKindOccRn :: RdrName -> RnM Name
lookupKindOccRn rdr_name = do
  mb_gre <- lookupOccRn_maybe rdr_name
  case mb_gre of
    Just gre -> return $ greName gre
    Nothing -> unboundName (LF WL_Anything WL_Anywhere) rdr_name

lookupOccRnX_maybe
  :: (RdrName -> RnM (Maybe r)) -> (GlobalRdrElt -> RnM r) -> RdrName -> RnM (Maybe r)
lookupOccRnX_maybe globalLookup wrapper rdr_name = runMaybeT . msum . map MaybeT $
  [ do { res <- lookupLocalOccRn_maybe rdr_name
       ; case res of
           Nothing -> return Nothing
           Just nm -> let gre = mkLocalVanillaGRE NoParent nm
                      in Just <$> wrapper gre }
  , globalLookup rdr_name ]

lookupOccRn_maybe :: RdrName -> RnM (Maybe GlobalRdrElt)
lookupOccRn_maybe = lookupOccRnX_maybe (lookupGlobalOccRn_maybe $ RelevantGREs False) return 

lookupExprOccRn :: RdrName -> RnM (Maybe GlobalRdrElt)
lookupExprOccRn rdr_name = 
  lookupOccRnX_maybe lookupExpr_helper return rdr_name
  where
    lookupExpr_helper :: RdrName -> RnM (Maybe GlobalRdrElt)
    lookupExpr_helper rdr_name =
      lookupExactOrOrig_maybe rdr_name id $ lookupGreRn_maybe (RelevantGREs False) rdr_name

lookupGlobalOccRn_maybe :: WhichGREs GREInfo -> RdrName -> RnM (Maybe GlobalRdrElt)
lookupGlobalOccRn_maybe which_gres rdr_name =
  lookupExactOrOrig_maybe rdr_name id $
  lookupGlobalOccRn_base which_gres rdr_name

lookupGlobalOccRn_base :: WhichGREs GREInfo -> RdrName -> RnM (Maybe GlobalRdrElt)
lookupGlobalOccRn_base which_gres rdr_name = runMaybeT . MaybeT $
  lookupGreRn_maybe which_gres rdr_name

lookupInfoOccRn ::RdrName -> RnM [Name]
lookupInfoOccRn rdr_name = lookupExactOrOrig rdr_name (\gre -> [greName gre]) $ do
  rdr_env <- getGlobalRdrEnv
  let nms = map greName $ lookupGRE rdr_env (LookupRdrName rdr_name (RelevantGREs False))
  return nms

data GreLookupResult
  = GreNotFound
  | OneNameMatch GlobalRdrElt
  | MultipleNames (NE.NonEmpty GlobalRdrElt)

lookupGreRn_maybe :: WhichGREs GREInfo -> RdrName -> RnM (Maybe GlobalRdrElt)
lookupGreRn_maybe which_gres rdr_name = do
  res <- lookupGreRn_helper which_gres rdr_name
  case res of
    OneNameMatch gre -> return $ Just gre
    MultipleNames gres -> do
      traceRn "lookupGreRn_maybe:NameClash" (ppr gres)
      addNameClashErrRn rdr_name gres
      return $ Just $ NE.head gres
    GreNotFound -> return Nothing

lookupGreRn_helper :: WhichGREs GREInfo -> RdrName -> RnM GreLookupResult
lookupGreRn_helper which_gres rdr_name = do
  env <- getGlobalRdrEnv
  case lookupGRE env (LookupRdrName rdr_name which_gres) of
    [] -> return GreNotFound
    [gre] -> do addUsedGRE gre
                return (OneNameMatch gre)
    gre:others -> return $ MultipleNames $ gre NE.:| others

addUsedGRE :: GlobalRdrElt -> RnM ()
addUsedGRE gre = when (isImportedGRE gre) $ do
  env <- getGblEnv
  traceRn "addUsedGRE" (ppr $ greName gre)
  updTcRef (tcg_used_gres env) (gre :)

lookupGREInfo :: HasDebugCallStack => CsEnv -> Name -> GREInfo
lookupGREInfo cs_env nm
  | Just ty_thing <- wiredInNameTyThing_maybe nm
  = tyThingGREInfo ty_thing
  | otherwise
  = case nameModule_maybe nm of
      Nothing -> UnboundGRE
      Just mod -> unsafePerformIO $ do
        _ <- initIfaceLoad cs_env $
             loadInterface (text "lookupGREInfo" <+> parens (ppr nm))
             mod ImportBySystem
        mb_ty_thing <- lookupType cs_env nm
        case mb_ty_thing of
          Nothing -> pprPanic "lookupGREInfo" $
                     vcat [ text "lookup failed:" <+> ppr nm ]
          Just ty_thing -> return $ tyThingGREInfo ty_thing

data CsSigCtxt
  = TopSigCtxt NameSet
  | LocalBindCtxt NameSet

instance Outputable CsSigCtxt where
  ppr (TopSigCtxt ns) = text "TopSigCtxt" <+> ppr ns
  ppr (LocalBindCtxt ns) = text "LocalBindCtxt" <+> ppr ns

lookupSigOccRnN :: CsSigCtxt -> Sig Ps -> LocatedN RdrName -> RnM (LocatedN Name)
lookupSigOccRnN ctxt sig = lookupSigCtxtOccRn ctxt (csSigDoc sig)

lookupSigCtxtOccRn
  :: CsSigCtxt -> SDoc -> GenLocated (EpAnn ann) RdrName -> RnM (GenLocated (EpAnn ann) Name)
lookupSigCtxtOccRn ctxt what = wrapLocMA $ \ rdr_name -> do
  let also_try_tycons = False
  mb_names <- lookupBindGroupOcc ctxt what rdr_name also_try_tycons NoNamespaceSpecifier
  case mb_names of
    Right name NE.:| rest -> do
      massertPpr (null rest) $
        vcat (text "lookupSigCtxtOccRn" <+> ppr name
              : map (either (pprScopeError rdr_name) ppr) rest)
      return name
    Left err NE.:| _ -> do
      addErr (mkTcRnNotInScope rdr_name err)
      return (mkUnboundNameRdr rdr_name)

lookupBindGroupOcc
  :: CsSigCtxt
  -> SDoc
  -> RdrName
  -> Bool
  -> NamespaceSpecifier
  -> RnM (NE.NonEmpty (Either NotInScopeError Name))
lookupBindGroupOcc ctxt what rdr_name also_try_tycon_ns ns_spec 
  | Just n <- isExact_maybe rdr_name
  = do mb_gre <- lookupExactOcc_either n
       return $ case mb_gre of
         Left err -> NE.singleton $ Left err
         Right gre -> finish (NoExactName $ greName gre) gre
  | Just (rdr_mod, rdr_occ) <- isOrig_maybe rdr_name
  = NE.singleton . Right <$> lookupOrig rdr_mod rdr_occ
  | otherwise
  = case ctxt of
      TopSigCtxt ns -> lookup_top (elem_name_set_with_namespace ns)
      LocalBindCtxt ns -> lookup_group ns
  where
    elem_name_set_with_namespace ns n = check_namespace n && (n `elemNameSet` ns)

    check_namespace = coveredByNamespaceSpecifier ns_spec . nameNameSpace

    namespace = occNameSpace occ
    occ = rdrNameOcc rdr_name
    relevant_gres = RelevantGREs also_try_tycon_ns
    ok_gre = greIsRelevant relevant_gres namespace

    finish err gre
      | ok_gre gre = NE.singleton (Right $ greName gre)
      | otherwise = NE.singleton (Left err)

    lookup_top keep_me = do
      env <- getGlobalRdrEnv
      let occ = rdrNameOcc rdr_name
          all_gres = lookupGRE env (LookupOccName occ relevant_gres)
          names_in_scope = map greName $ filter (ok_gre <&&> isLocalGRE) $ globalRdrEnvElts env
          candidates_msg = candidates names_in_scope
      case filter (keep_me . greName) all_gres of
        [] | null all_gres -> bale_out_with candidates_msg
           | otherwise -> bale_out_with local_msg
        (gre1:gres) -> return (fmap (Right . greName) (gre1 NE.:| gres))

    lookup_group bound_names = do
      mname <- lookupLocalOccRn_maybe rdr_name
      env <- getLocalRdrEnv
      let candidates_msg = candidates $ localRdrEnvElts env
      case mname of
        Just n | n `elemNameSet` bound_names -> return $ NE.singleton $ Right n
               | otherwise -> bale_out_with local_msg
        Nothing -> bale_out_with candidates_msg

    bale_out_with hints = return $ NE.singleton $ Left $ MissingBinding what hints

    local_msg = [SuggestMoveToDeclarationSite what rdr_name]

    candidates :: [Name] -> [CsHint]
    candidates names_in_scope
      | (nm : nms) <- map SimilarName similar_names
      = [SuggestSimilarNames rdr_name (nm NE.:| nms)]
      | otherwise
      = []
      where
        similar_names = fuzzyLookup (unpackFS $ occNameFS $ rdrNameOcc rdr_name)
                      $ map (\x -> ((unpackFS $ occNameFS $ nameOccName x), x))
                        names_in_scope

{- *********************************************************************
*                                                                      *
              Literal syntax desugaring
*                                                                      *
********************************************************************* -}

-- this is rebindable syntax in GHC, but we handle things differently

lookupSyntaxName :: Name -> RnM (Name, FreeVars)
lookupSyntaxName std_name = do
  return (std_name, emptyFVs)

lookupSyntaxExpr :: Name -> RnM (CsExpr Rn, FreeVars)
lookupSyntaxExpr std_name = do
  (name, fvs) <- lookupSyntaxName std_name
  return (nl_CsVar name, fvs)

lookupSyntax :: Name -> RnM (SyntaxExpr Rn, FreeVars)
lookupSyntax std_name = do
  (expr, fvs) <- lookupSyntaxExpr std_name
  return (mkSyntaxExpr expr, fvs)
