module CSlash.Unit.State
  ( module CSlash.Unit.Info
  , module CSlash.Unit.State
  ) where

import Prelude hiding ((<>))

import CSlash.Driver.DynFlags

import CSlash.Platform
import CSlash.Platform.Ways

-- import GHC.Unit.Database
import CSlash.Unit.Info
-- import GHC.Unit.Ppr
import CSlash.Unit.Types
import CSlash.Unit.Module
import CSlash.Unit.Home

import CSlash.Types.Unique.FM
import CSlash.Types.Unique.DFM
import CSlash.Types.Unique.Set
import CSlash.Types.Unique.DSet
import CSlash.Types.Unique.Map
import CSlash.Types.Unique
import CSlash.Types.PkgQual

import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Outputable as Outputable
import CSlash.Data.Maybe

import System.Environment ( getEnv )
import CSlash.Data.FastString
-- import qualified GHC.Data.ShortText as ST
import CSlash.Utils.Logger
import CSlash.Utils.Error
import CSlash.Utils.Exception

import System.Directory
import System.FilePath as FilePath
import Control.Monad
import Data.Graph (stronglyConnComp, SCC(..))
import Data.Char ( toUpper )
import Data.List ( intersperse, partition, sortBy, isSuffixOf, sortOn )
import Data.Set (Set)
import Data.Monoid (First(..))
import qualified Data.Semigroup as Semigroup
import qualified Data.Set as Set
-- import GHC.LanguageExtensions
import Control.Applicative

data ModuleOrigin
  = ModHidden
  | ModUnusable !UnusableUnit
  | ModOrigin
    { fromOrigUnit :: Maybe Bool
    , fromExposedReexport :: [UnitInfo]
    , fromHiddenReexport :: [UnitInfo]
    , fromPackageFlag :: Bool
    }

data UnusableUnit = UnusableUnit
  { uuUnit :: !Unit
  , uuReason :: !UnusableUnitReason
  , uuIsReexport :: !Bool
  }

instance Outputable ModuleOrigin where
  ppr ModHidden = text "hidden module"
  ppr (ModUnusable _) = text "unusable module"
  ppr (ModOrigin e res rhs f) = sep (punctuate comma (
                                        (case e of
                                           Nothing -> []
                                           Just False -> [text "hidden package"]
                                           Just True -> [text "exposed package"])
                                        ++ (if null res
                                             then []
                                             else [text "reexported by" <+>
                                                   sep (map (ppr . mkUnit) res)])
                                        ++ (if null rhs
                                             then []
                                             else [text "hidden reexport by" <+>
                                                   sep (map (ppr . mkUnit) res)])
                                        ++ (if f then [text "package flag"] else [])))

instance Semigroup ModuleOrigin where
  x@(ModOrigin e res rhs f) <> y@(ModOrigin e' res' rhs' f') =
    ModOrigin (g e e') (res ++ res') (rhs ++ rhs') (f || f')
    where
      g (Just b) (Just b')
        | b == b' = Just b
        | otherwise = pprPanic "ModOrigin: package both exposed/hidden" $
                      text "x: " <> ppr x $$ text "y: " <> ppr y
      g Nothing x = x
      g x Nothing = x

  x <> y = pprPanic "ModOrigin: module origin mismath" $
           text "x: " <> ppr x $$ text "y: " <> ppr y

instance Monoid ModuleOrigin where
  mempty = ModOrigin Nothing [] [] False
  mappend = (Semigroup.<>)

originVisible :: ModuleOrigin -> Bool
originVisible ModHidden = False
originVisible (ModUnusable _) = False
originVisible (ModOrigin b res _ f) = b == Just True || not (null res) || f

originEmpty :: ModuleOrigin -> Bool
originEmpty (ModOrigin Nothing [] [] False) = True
originEmpty _ = False

type PreloadUnitClosure = UniqSet UnitId

type ModuleNameProvidersMap = UniqMap ModuleName (UniqMap Module ModuleOrigin)

data UnitState = UnitState
  { unitInfoMap :: UnitInfoMap
  , preloadClosure :: PreloadUnitClosure
  , packageNameMap :: UniqFM PackageName UnitId
  , wireMap :: UniqMap UnitId UnitId
  , unwireMap :: UniqMap UnitId UnitId
  , preloadUnits :: [UnitId]
  , explicitUnits :: [(Unit, Maybe PackageArg)]
  , homeUnitDepends :: [UnitId]
  , moduleNameProvidersMap :: !ModuleNameProvidersMap
  , requirementContext :: UniqMap ModuleName [InstantiatedModule]
  , allowVirtualUnits :: !Bool
  }

emptyUnitState :: UnitState
emptyUnitState = UnitState
  { unitInfoMap = emptyUniqMap
  , preloadClosure = emptyUniqSet
  , packageNameMap = emptyUFM
  , wireMap = emptyUniqMap
  , unwireMap = emptyUniqMap
  , preloadUnits = []
  , explicitUnits = []
  , homeUnitDepends = []
  , moduleNameProvidersMap = emptyUniqMap
  , requirementContext = emptyUniqMap
  , allowVirtualUnits = False
  }

data UnitDatabase unit = UnitDatbase
  { unitDatabasePath :: FilePath
  , unitDatabaseUnits :: [GenUnitInfo unit]
  }

type UnitInfoMap = UniqMap UnitId UnitInfo

lookupUnit :: UnitState -> Unit -> Maybe UnitInfo
lookupUnit pkgs = lookupUnit' (allowVirtualUnits pkgs) (unitInfoMap pkgs) (preloadClosure pkgs)

lookupUnit' :: Bool -> UnitInfoMap -> PreloadUnitClosure -> Unit -> Maybe UnitInfo
lookupUnit' allowOnTheFlyInst pkg_map closure u = case u of
  HoleUnit -> error "Hole unit"
  RealUnit i -> lookupUniqMap pkg_map (unDefinite i)
  VirtUnit i
    | allowOnTheFlyInst
      -> fmap (renameUnitInfo pkg_map closure (instUnitInsts i))
         (lookupUniqMap pkg_map (instUnitInstanceOf i))
    | otherwise
      -> lookupUniqMap pkg_map (virtualUnitId i)

lookupUnitId :: UnitState -> UnitId -> Maybe UnitInfo
lookupUnitId state uid = lookupUnitId' (unitInfoMap state) uid

lookupUnitId' :: UnitInfoMap -> UnitId -> Maybe UnitInfo
lookupUnitId' db uid = lookupUniqMap db uid

listUnitInfo :: UnitState -> [UnitInfo]
listUnitInfo state = nonDetEltsUniqMap (unitInfoMap state)

renameUnitInfo
  :: UnitInfoMap -> PreloadUnitClosure -> [(ModuleName, Module)] -> UnitInfo -> UnitInfo
renameUnitInfo pkg_map closure insts conf =
  let hsubst = listToUFM insts
      smod = renameHoleModule' pkg_map closure hsubst
      new_insts = map (\(k, v) -> (k, smod v)) (unitInstantiations conf)
  in conf
     { unitInstantiations = new_insts
     , unitExposedModules = map (\(mod_name, mb_mod) -> (mod_name, fmap smod mb_mod))
                            (unitExposedModules conf)
     }

comparing :: Ord a => (t -> a) -> t -> t -> Ordering
comparing f a b = f a `compare` f b

data UnusableUnitReason
  = IgnoredWithFlag
  | BrokenDependencies [UnitId]
  | CyclicDependencies [UnitId]
  | IgnoredDependencies [UnitId]
  | ShadowedDependencies [UnitId]

-- -----------------------------------------------------------------------------
-- Package Utils

data LookupResult
  = LookupFound Module (UnitInfo, ModuleOrigin)
  | LookupMultiple [(Module, ModuleOrigin)]
  | LookupHidden [(Module, ModuleOrigin)] [(Module, ModuleOrigin)]
  | LookupUnusable [(Module, ModuleOrigin)]
  | LookupNotFound [ModuleSuggestion]

data ModuleSuggestion
  = SuggestVisible ModuleName Module ModuleOrigin
  | SuggestHidden ModuleName Module ModuleOrigin

lookupModuleWithSuggestions :: UnitState -> ModuleName -> PkgQual -> LookupResult
lookupModuleWithSuggestions pkgs
  = lookupModuleWithSuggestions' pkgs (moduleNameProvidersMap pkgs)

lookupModuleWithSuggestions'
  :: UnitState -> ModuleNameProvidersMap -> ModuleName -> PkgQual -> LookupResult
lookupModuleWithSuggestions' pkgs mod_map m mb_pn
  = case lookupUniqMap mod_map m of
      Nothing -> LookupNotFound suggestions
      Just xs -> case foldl' classify ([], [], [], []) (sortOn fst $ nonDetUniqMapToList xs) of
        ([], [], [], []) -> LookupNotFound suggestions
        (_, _, _, [(m,o)]) -> LookupFound m (mod_unit m, o)
        (_, _, _, exposed@(_:_)) -> LookupMultiple exposed
        ([], [], unusable@(_:_), []) -> LookupUnusable unusable
        (hidden_pkg, hidden_mod, _, []) -> LookupHidden hidden_pkg hidden_mod
  where
    classify (hidden_pkg, hidden_mod, unusable, exposed) (m, origin0) =
      let origin = filterOrigin mb_pn (mod_unit m) origin0
          x = (m, origin)
      in case origin of
           ModHidden
             -> (hidden_pkg, x:hidden_mod, unusable, exposed)
           ModUnusable _
             -> (hidden_pkg, hidden_mod, x:unusable, exposed)
           _ | originEmpty origin
             -> (hidden_pkg, hidden_mod, unusable, exposed)
             | originVisible origin
             -> (hidden_pkg, hidden_mod, unusable, x:exposed)
             | otherwise
             -> (x:hidden_pkg, hidden_mod, unusable, exposed)

    unit_lookup p = lookupUnit pkgs p `orElse`
                    pprPanic "lookupModuleWithSuggestions" (ppr p <+> ppr m)

    mod_unit = unit_lookup . moduleUnit

    filterOrigin :: PkgQual -> UnitInfo -> ModuleOrigin -> ModuleOrigin
    filterOrigin NoPkgQual _ o = o
    filterOrigin (ThisPkg _) _ o = o
    filterOrigin (OtherPkg u) pkg o =
      let match_pkg p = u == unitId p
      in case o of
           ModHidden
             | match_pkg pkg -> ModHidden
             | otherwise -> mempty
           ModUnusable _
             | match_pkg pkg -> o
             | otherwise -> mempty
           ModOrigin { fromOrigUnit = e, fromExposedReexport = res, fromHiddenReexport = rhs }
             -> ModOrigin
                { fromOrigUnit = if match_pkg pkg then e else Nothing
                , fromExposedReexport = filter match_pkg res
                , fromHiddenReexport = filter match_pkg rhs
                , fromPackageFlag = False
                }

    suggestions = fuzzyLookup (moduleNameString m) all_mods

    all_mods :: [(String, ModuleSuggestion)]
    all_mods = sortBy (comparing fst) $
      [ (moduleNameString m, suggestion)
      | (m, e) <- nonDetUniqMapToList (moduleNameProvidersMap pkgs)
      , suggestion <- map (getSuggestion m) (nonDetUniqMapToList e)
      ]

    getSuggestion name (mod, origin) =
      (if originVisible origin then SuggestVisible else SuggestHidden)
      name mod origin

-- -----------------------------------------------------------------------------
-- Displaying packages

pprUnits :: UnitState -> SDoc
pprUnits = pprUnitsWith pprUnitInfo

pprUnitsWith :: (UnitInfo -> SDoc) -> UnitState -> SDoc
pprUnitsWith pprIPI pkgstate =
  vcat (intersperse (text "---") (map pprIPI (listUnitInfo pkgstate)))

pprUnitsSimple :: UnitState -> SDoc
pprUnitsSimple = pprUnitsWith pprIPI
  where
    pprIPI ipi = let i = unitIdFS (unitId ipi)
                     e = if unitIsExposed ipi then text "E" else text " "
                 in e <> text "  " <> ftext i

improveUnit' :: UnitInfoMap -> PreloadUnitClosure -> Unit -> Unit
improveUnit' _ _ uid@(RealUnit _) = uid
improveUnit' pkg_map closure uid =
  case lookupUnit' False pkg_map closure uid of
    Nothing -> uid
    Just pkg -> if unitId pkg `elementOfUniqSet` closure
                then mkUnit pkg
                else uid

type ShHoleSubst = ModuleNameEnv Module

renameHoleModule' :: UnitInfoMap -> PreloadUnitClosure -> ShHoleSubst -> Module -> Module
renameHoleModule' pkg_map closure env m
  | not (isHoleModule m)
  = let uid = renameHoleUnit' pkg_map closure env (moduleUnit m)
    in mkModule uid (moduleName m)
  | Just m' <- lookupUFM env (moduleName m) = m'
  | otherwise = m

renameHoleUnit' :: UnitInfoMap -> PreloadUnitClosure -> ShHoleSubst -> Unit -> Unit
renameHoleUnit' pkg_map closure env uid =
  case uid of
    (VirtUnit InstantiatedUnit { instUnitInstanceOf = cid
                               , instUnitInsts = insts
                               , instUnitHoles = fh })
      -> if isNullUFM (intersectUFM_C const (udfmToUfm (getUniqDSet fh)) env)
         then uid
         else improveUnit' pkg_map closure $
              mkVirtUnit cid
              (map (\(k, v) -> (k, renameHoleModule' pkg_map closure env v)) insts)
    _ -> uid
