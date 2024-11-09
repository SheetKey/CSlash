{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module CSlash.Iface.Errors.Ppr where

import Prelude hiding ((<>))

import CSlash.Types.Error
import CSlash.Types.Hint.Ppr () 
import CSlash.Types.Error.Codes
import CSlash.Types.Name
import CSlash.Types.TyThing

import CSlash.Unit.State
import CSlash.Unit.Module

import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import CSlash.Iface.Errors.Types

defaultIfaceMessageOpts :: IfaceMessageOpts
defaultIfaceMessageOpts = IfaceMessageOpts { ifaceShowTriedFiles = False }

instance HasDefaultDiagnosticOpts IfaceMessageOpts where
  defaultOpts = defaultIfaceMessageOpts

instance Diagnostic IfaceMessage where
  type DiagnosticOpts IfaceMessage = IfaceMessageOpts

  diagnosticMessage opts reason = mkSimpleDecorated $
    interfaceErrorDiagnostic opts reason

  diagnosticReason = interfaceErrorReason

  diagnosticHints = interfaceErrorHints

  diagnosticCode = constructorCode

interfaceErrorHints :: IfaceMessage -> [CsHint]
interfaceErrorHints _ = noHints

interfaceErrorReason :: IfaceMessage -> DiagnosticReason
interfaceErrorReason _ = ErrorWithoutFlag

data FindOrLoad = Find | Load

data AmbiguousOrMissing = AoM_Ambiguous | AoM_Missing

prettyCantFindWhat :: FindOrLoad -> FindingModuleOrInterface -> AmbiguousOrMissing -> SDoc
prettyCantFindWhat Find FindingModule AoM_Missing = text "Could not find module"
prettyCantFindWhat Load FindingModule AoM_Missing = text "Could not load module"
prettyCantFindWhat _ FindingInterface AoM_Missing = text "Failed to load interface for "
prettyCantFindWhat _ FindingModule AoM_Ambiguous = text "Ambiguous module name"
prettyCantFindWhat _ FindingInterface AoM_Ambiguous = text "Ambiguous interface for"

isAmbiguousInstalledReason :: CantFindInstalledReason -> AmbiguousOrMissing
isAmbiguousInstalledReason (MultiplePackages {}) = AoM_Ambiguous
isAmbiguousInstalledReason _ = AoM_Missing

isLoadOrFindReason :: CantFindInstalledReason -> FindOrLoad
isLoadOrFindReason NotAModule = Find
isLoadOrFindReason (GenericMissing a b c _) | null a && null b && null c = Find
isLoadOrFindReason (ModuleSuggestion {}) = Find
isLoadOrFindReason _ = Load

cantFindError :: IfaceMessageOpts -> FindingModuleOrInterface -> CantFindInstalled -> SDoc
cantFindError opts = cantFindErrorX
  (const empty) (mayShowLocations "-v" (ifaceShowTriedFiles opts))

mayShowLocations :: String -> Bool -> [FilePath] -> SDoc
mayShowLocations option verbose files
  | null files = empty
  | not verbose = text "Use" <+> text option <+> text "to see a list of the files searched for."
  | otherwise = hang (text "Locations searched:") 2 $ vcat (map text files)

cantFindErrorX
  :: (UnitInfo -> SDoc)
  -> ([FilePath] -> SDoc)
  -> FindingModuleOrInterface
  -> CantFindInstalled
  -> SDoc
cantFindErrorX pkg_hidden_hint may_show_locations mod_or_interface cfi =
  let (CantFindInstalled mod_name cfir) = cfi
      ambig = isAmbiguousInstalledReason cfir
      find_or_load = isLoadOrFindReason cfir
      ppr_what = prettyCantFindWhat find_or_load mod_or_interface ambig
  in (ppr_what <+> quotes (ppr mod_name) <> dot) $$
     case cfir of
       NoUnitIdMatching pkg cands ->
         let looks_like_srcpkgid = case cands of
               pkg:pkgs -> parens $ text "This unit ID looks like the source package ID;"
                                 $$ text "the real unit ID is"
                                 <+> quotes (ftext (unitIdFS (unitId pkg)))
                                 $$ (if null pkgs then empty
                                      else text "and" <+> int (length pkgs)
                                                      <+> text "other candidate" <> plural pkgs)
               [] -> empty
         in hsep [ text "no unit id matching" <+> quotes (ppr pkg)
                 , text "was found" ] $$ looks_like_srcpkgid
       MissingPackageFiles pkg files ->
         text "There are files mmissing in the " <> quotes (ppr pkg) <+>
         text "package." $$
         may_show_locations files
       MissingPackageWayFiles build pkg files ->
         text "Perhaps you haven't installed the " <> text build <+>
         text "libraries for package " <> quotes (ppr pkg) <> char '?' $$
         may_show_locations files
       ModuleSuggestion ms fps ->
         let pp_suggestions sugs
               | null sugs = empty
               | otherwise = hang (text "Perhaps you meant") 2 (vcat (map pp_sugg sugs))

             pp_sugg (SuggestVisible m mod o) = ppr m <+> provenance o
               where provenance ModHidden = empty
                     provenance (ModUnusable _) = empty
                     provenance (ModOrigin { fromOrigUnit = e
                                           , fromExposedReexport = res
                                           , fromPackageFlag = f })
                       | Just True <- e
                       = parens (text "from" <+> ppr (moduleUnit mod))
                       | f && moduleName mod == m
                       = parens (text "from" <+> ppr (moduleUnit mod))
                       | (pkg:_) <- res
                       = parens (text "from" <+> ppr (mkUnit pkg)
                                 <> comma <+> text "reexporting" <+> ppr mod)
                       | f = parens (text "defined via package flags to be" <+> ppr mod)
                       | otherwise = empty
             pp_sugg (SuggestHidden m mod o) = ppr m <+> provenance o
               where provenance ModHidden = empty
                     provenance (ModUnusable _) = empty
                     provenance (ModOrigin { fromOrigUnit = e
                                           , fromHiddenReexport = rhs })
                       | Just False <- e
                       = parens (text "needs flag -package-id"
                                 <+> ppr (moduleUnit mod))
                       | (pkg:_) <- rhs
                       = parens (text "needs flag -package-id"
                                 <+> ppr (mkUnit pkg))
                       | otherwise = empty
         in pp_suggestions ms $$ may_show_locations fps
       NotAModule -> text "It is not a module in the current program, or in any known package."
       CouldntFindInFiles fps -> vcat (map text fps)
       MultiplePackages mods
         | Just pkgs <- unambiguousPackages
           -> sep [ text "it was found in multiple packages:"
                  , hsep (map ppr pkgs) ]
         | otherwise -> vcat (map pprMod mods)
         where
           unambiguousPackages = foldl' unambiguousPackage (Just []) mods
           unambiguousPackage (Just xs) (m, ModOrigin (Just _) _ _ _) = Just (moduleUnit m : xs)
           unambiguousPackage _ _ = Nothing
       GenericMissing pkg_hiddens mod_hiddens unusables files ->
         vcat (map pkg_hidden pkg_hiddens) $$
         vcat (map mod_hidden mod_hiddens) $$
         vcat (map unusable unusables) $$
         may_show_locations files
  where
    pprMod (m, o) = text "it is bounds as" <+> ppr m <+> text "by" <+> pprOrigin m o

    pprOrigin _ ModHidden = panic "cantFindErr: bound by mod hidden"
    pprOrigin _ (ModUnusable _) = panic "cantFindErr: bound by mod unusable"
    pprOrigin m (ModOrigin e res _ f) = sep $ punctuate comma $
      if e == Just True
      then [text "package" <+> ppr (moduleUnit m)]
      else [] ++ map ((text "a reexport in package" <+>) . ppr . mkUnit) res
              ++ if f then [text "a package flag"] else []

    pkg_hidden (uid, uif) = text "It is a member of the hidden package"
                            <+> quotes (ppr uid)
                            <> dot $$ maybe empty pkg_hidden_hint uif

    mod_hidden pkg = text "it is a hidden module in the package" <+> quotes (ppr pkg)

    unusable (UnusableUnit unit reason reexport)
      = text "It is " <> (if reexport then text "reexported from the package"
                           else text "a member of the package")
        <+> quotes (ppr unit)
        $$ pprReason (text "which is") reason

interfaceErrorDiagnostic :: IfaceMessageOpts -> IfaceMessage -> SDoc
interfaceErrorDiagnostic opts = \case
  Can'tFindNameInInterface name relevant_tyThings ->
    missingDeclInInterface name relevant_tyThings
  Can'tFindInterface err looking_for ->
    hangNotEmpty (lookingForHerald looking_for) 2 (missingInterfaceErrorDiagnostic opts err)
  CircularImport mod ->
    text "Circular imports: module" <+> quotes (ppr mod)
    <+> text "depends on itself"

lookingForHerald :: InterfaceLookingFor -> SDoc
lookingForHerald _ = empty

readInterfaceErrorDiagnostic :: ReadInterfaceError -> SDoc
readInterfaceErrorDiagnostic = \case
  ExceptionOccurred fp ex ->
    hang (text "Exception when reading interface file " <+> text fp)
    2 (text (show ex))
  HiModuleNameMismatchWarn _ m1 m2 -> hiModuleNameMismatchWarn m1 m2

missingInterfaceErrorDiagnostic :: IfaceMessageOpts -> MissingInterfaceError -> SDoc
missingInterfaceErrorDiagnostic opts reason =
  case reason of
    HomeModError im ml -> homeModError im ml
    DynamicHashMismatchError m ml -> dynamicHashMismatchError m ml
    CantFindErr us module_or_interface cfi ->
      pprWithUnitState us $ cantFindError opts module_or_interface cfi
    BadIfaceFile rie -> readInterfaceErrorDiagnostic rie
    FailedToLoadDynamicInterface wanted_mod err ->
      hang (text "Failed to load dynamic interface file for" <+> ppr wanted_mod <> colon)
      2 (readInterfaceErrorDiagnostic err)

hiModuleNameMismatchWarn :: Module -> Module -> SDoc
hiModuleNameMismatchWarn requested_mod read_mod
  | moduleUnit requested_mod == moduleUnit read_mod
  = sep [ text "Interface file contains module" <+> quotes (ppr read_mod) <> comma
        , text "but we were expecting module" <+> quotes (ppr requested_mod)
        , sep [ text "Probable cause: the source code which generated interface file"
              , text "has an incompatible module name"
              ]
        ]
  | otherwise
  = withPprStyle (mkUserStyle alwaysQualify AllTheWay) $
    hsep [ text "Something is amiss; requested module "
         , ppr requested_mod
         , text "differs from the name found in the interface file"
         , ppr read_mod
         , parens (text "if these names look the same, try again with -dppr-debug")
         ]

dynamicHashMismatchError :: Module -> ModLocation -> SDoc
dynamicHashMismatchError wanted_mod loc =
  vcat [ text "Dynamic hash doesn't match for" <+> quotes (ppr wanted_mod)
       , text "Normal interface file from" <+> text (ml_hi_file loc)
       , text "Dynamic interface file from" <+> text (ml_dyn_hi_file loc)
       , text "You probably need to recompile" <+> quotes (ppr wanted_mod) ]

homeModError :: InstalledModule -> ModLocation -> SDoc
homeModError mod location = text "attempting to use module " <> quotes (ppr mod)
  <> (case ml_cs_file location of
        Just file -> space <> parens (text file)
        Nothing -> empty)
  <+> text "which is not loaded"

missingDeclInInterface :: Name -> [TyThing] -> SDoc
missingDeclInInterface name things =
  whenPprDebug (found_things $$ empty) $$
  hang (text "Can't find interface-file declaration for"
        <+> pprNameSpace (nameNameSpace name) <+> ppr name)
  2 (vcat [ text "Probable cause: inconsistent .hi file"
          , text "Use -ddump-if-trace to get an idea of which file caused the error" ])
  where
    found_things =
      hang (text "Found the following declaration in" <+> ppr (nameModule name) <> colon)
      2 (vcat (map ppr things))
           
