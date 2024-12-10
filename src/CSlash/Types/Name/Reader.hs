{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Types.Name.Reader where

import Prelude hiding ((<>))

import CSlash.Language.Syntax.Module.Name

import CSlash.Data.Bag
import CSlash.Data.Maybe
import CSlash.Data.FastString

import CSlash.Types.Avail
import CSlash.Types.Basic
import CSlash.Types.GREInfo
import CSlash.Types.SrcLoc
import CSlash.Types.Unique
import CSlash.Types.Unique.Set
import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.Name.Occurrence
import CSlash.Unit.Types
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc as Utils

import Control.DeepSeq
import Data.Data
import Data.List (sort)
import qualified Data.List.NonEmpty as NE
import qualified Data.Semigroup as S

data RdrName
  = Unqual OccName
  | Qual ModuleName OccName
  | Orig Module OccName
  | Exact Name
  deriving Data

unknownToVar :: RdrName -> RdrName
unknownToVar (Unqual (OccName UNKNOWN_NS fs)) = Unqual (OccName VarName fs)
unknownToVar (Qual mn (OccName UNKNOWN_NS fs)) = Qual mn (OccName VarName fs)
unknownToVar other = pprPanic "unknownToVar" (ppr other)

unknownToTv :: RdrName -> RdrName
unknownToTv (Unqual (OccName UNKNOWN_NS fs)) = Unqual (OccName TvName fs)  
unknownToTv (Qual mn (OccName UNKNOWN_NS fs)) = Qual mn (OccName TvName fs)
unknownToTv other = pprPanic "unknownToTv" (ppr other)

unknownToKv :: RdrName -> RdrName
unknownToKv (Unqual (OccName UNKNOWN_NS fs)) = Unqual (OccName KvName fs)  
unknownToKv (Qual mn (OccName UNKNOWN_NS fs)) = Qual mn (OccName KvName fs)
unknownToKv other = pprPanic "unknownToKv" (ppr other)

unknownToData :: RdrName -> RdrName
unknownToData (Unqual (OccName UNKNOWN_NS fs)) = Unqual (OccName DataName fs)  
unknownToData (Qual mn (OccName UNKNOWN_NS fs)) = Qual mn (OccName DataName fs)
unknownToData other = pprPanic "unknownToData" (ppr other)

unknownToTcCls :: RdrName -> RdrName
unknownToTcCls (Unqual (OccName UNKNOWN_NS fs)) = Unqual (OccName TcClsName fs)  
unknownToTcCls (Qual mn (OccName UNKNOWN_NS fs)) = Qual mn (OccName TcClsName fs)
unknownToTcCls other = pprPanic "unknownToTcCls" (ppr other)

instance HasOccName RdrName where
  occName = rdrNameOcc

rdrNameOcc :: RdrName -> OccName
rdrNameOcc (Qual _ occ) = occ
rdrNameOcc (Unqual occ) = occ
rdrNameOcc (Orig _ occ) = occ
rdrNameOcc (Exact name) = nameOccName name

rdrNameSpace :: RdrName -> NameSpace
rdrNameSpace = occNameSpace . rdrNameOcc

mkRdrUnqual :: OccName -> RdrName
mkRdrUnqual occ = Unqual occ

mkRdrQual :: ModuleName -> OccName -> RdrName
mkRdrQual mod occ = Qual mod occ

mkUnqual :: NameSpace -> FastString -> RdrName
mkUnqual sp n = Unqual (mkOccNameFS sp n)

mkQual :: NameSpace -> (FastString, FastString) -> RdrName
mkQual sp (m, n) = Qual (mkModuleNameFS m) (mkOccNameFS sp n)

getRdrName :: NamedThing thing => thing -> RdrName
getRdrName name = nameRdrName (getName name)

nameRdrName :: Name -> RdrName
nameRdrName name = Exact name

nukeExact :: Name -> RdrName
nukeExact n
  | isExternalName n = Orig (nameModule n) (nameOccName n)
  | otherwise = Unqual (nameOccName n)

isRdrDataCon :: RdrName -> Bool
isRdrDataCon rn = isDataOcc (rdrNameOcc rn)

isRdrTyLvl :: RdrName -> Bool
isRdrTyLvl rn = let occ = rdrNameOcc rn in isTcOcc occ || isTvOcc occ

isRdrTc :: RdrName -> Bool
isRdrTc rn = isTcOcc (rdrNameOcc rn)

isRdrTyVar :: RdrName -> Bool
isRdrTyVar rn = isTvOcc (rdrNameOcc rn)

isRdrKiVar :: RdrName -> Bool
isRdrKiVar rn = isKvOcc (rdrNameOcc rn)

isRdrUnknown :: RdrName -> Bool
isRdrUnknown rn = isUnknownOcc (rdrNameOcc rn)

isUnqual :: RdrName -> Bool
isUnqual (Unqual _) = True
isUnqual _ = False

isQual :: RdrName -> Bool
isQual (Qual _ _) = True
isQual _ = False

isOrig_maybe :: RdrName -> Maybe (Module, OccName)
isOrig_maybe (Orig m n) = Just (m, n)
isOrig_maybe _ = Nothing

isExact :: RdrName -> Bool
isExact (Exact _) = True
isExact _ = False

isExact_maybe :: RdrName -> Maybe Name
isExact_maybe (Exact n) = Just n
isExact_maybe _ = Nothing

{- *********************************************************************
*                                                                      *
            Instances
*                                                                      *
********************************************************************* -}

instance Outputable RdrName where
  ppr (Exact name) = ppr name
  ppr (Unqual occ) = ppr occ
  ppr (Qual mod occ) = ppr mod <> dot <> ppr occ
  ppr (Orig mod occ) = getPprStyle (\sty -> pprModulePrefix sty mod occ <> ppr occ)

instance OutputableBndr RdrName where
  pprBndr _ n = ppr n

  pprInfixOcc rdr = pprInfixVar (isSymOcc (rdrNameOcc rdr)) (ppr rdr)
  pprPrefixOcc rdr
    | Just name <- isExact_maybe rdr = pprPrefixName name
    | otherwise = pprPrefixVar (isSymOcc (rdrNameOcc rdr)) (ppr rdr)

instance Eq RdrName where
  (Exact n1) == (Exact n2) = n1 == n2
  (Exact n1) == r2@(Orig _ _) = nukeExact n1 == r2
  r1@(Orig _ _) == (Exact n2) = r1 == nukeExact n2
  (Orig m1 o1) == (Orig m2 o2) = m1 == m2 && o1 == o2
  (Qual m1 o1) == (Qual m2 o2) = m1 == m2 && o1 == o2
  (Unqual o1) == (Unqual o2) = o1 == o2
  _ == _ = False

instance Ord RdrName where
  a <= b = case (a `compare` b) of
             GT -> False
             _ -> True
  a < b = case (a `compare` b) of
            LT -> True
            _ -> False
  a >= b = case (a `compare` b) of
             LT -> False
             _ -> True
  a > b = case (a `compare` b) of
            GT -> True
            _ -> False

  compare (Exact n1) (Exact n2) = n1 `compare` n2
  compare (Exact _) _ = LT

  compare (Unqual _) (Exact _) = GT
  compare (Unqual o1) (Unqual o2) = o1 `compare` o2
  compare (Unqual _) _ = LT

  compare (Qual _ _) (Exact _) = GT
  compare (Qual _ _) (Unqual _) = GT
  compare (Qual m1 o1) (Qual m2 o2) = compare o1 o2 S.<> compare m1 m2
  compare (Qual _ _) (Orig _ _) = LT

  compare (Orig m1 o1) (Orig m2 o2) = compare o1 o2 S.<> compare m1 m2
  compare (Orig _ _) _ = GT

{- *********************************************************************
*                                                                      *
                        LocalRdrEnv
*                                                                      *
********************************************************************* -}

data LocalRdrEnv = LRE
  { lre_env :: OccEnv Name
  , lre_in_scope :: NameSet
  }

emptyLocalRdrEnv :: LocalRdrEnv
emptyLocalRdrEnv = LRE
                   { lre_env = emptyOccEnv
                   , lre_in_scope = emptyNameSet }

extendLocalRdrEnvList :: LocalRdrEnv -> [Name] -> LocalRdrEnv
extendLocalRdrEnvList lre@(LRE { lre_env = env, lre_in_scope = ns }) names
  = lre { lre_env = extendOccEnvList env [(nameOccName n, n) | n <- names]
        , lre_in_scope = extendNameSetList ns names }

lookupLocalRdrEnv :: LocalRdrEnv -> RdrName -> Maybe Name
lookupLocalRdrEnv (LRE { lre_env = env, lre_in_scope = ns }) rdr
  | Unqual occ <- rdr
  = lookupOccEnv env occ
  | Exact name <- rdr
  , name `elemNameSet` ns
  = Just name
  | otherwise
  = Nothing

lookupLocalRdrOcc :: LocalRdrEnv -> OccName -> Maybe Name
lookupLocalRdrOcc (LRE { lre_env = env }) occ = lookupOccEnv env occ

elemLocalRdrEnv :: RdrName -> LocalRdrEnv -> Bool
elemLocalRdrEnv rdr_name (LRE { lre_env = env, lre_in_scope = ns })
  = case rdr_name of
      Unqual occ -> occ `elemOccEnv` env
      Exact name -> name `elemNameSet` ns
      Qual {} -> False
      Orig {} -> False
   
localRdrEnvElts :: LocalRdrEnv -> [Name]
localRdrEnvElts (LRE { lre_env = env }) = nonDetOccEnvElts env

inLocalRdrEnvScope :: Name -> LocalRdrEnv -> Bool
inLocalRdrEnvScope name (LRE { lre_in_scope = ns }) = name `elemNameSet` ns

{- *********************************************************************
*                                                                      *
                        GlobalRdrEnv
*                                                                      *
********************************************************************* -}

type GlobalRdrEnv = GlobalRdrEnvX GREInfo

type IfGlobalRdrEnv = GlobalRdrEnvX ()

type GlobalRdrEnvX info = OccEnv [GlobalRdrEltX info]

type GlobalRdrElt = GlobalRdrEltX GREInfo

data GlobalRdrEltX info = GRE
  { gre_name :: !Name
  , gre_par :: !Parent
  , gre_lcl :: !Bool
  , gre_imp :: !(Bag ImportSpec)
  , gre_info :: info
  }
  deriving (Data)

greName :: GlobalRdrEltX info -> Name
greName = gre_name

greNameSpace :: GlobalRdrEltX info -> NameSpace
greNameSpace = nameNameSpace . greName

greParent :: GlobalRdrEltX info -> Parent
greParent = gre_par

greInfo :: GlobalRdrElt -> GREInfo
greInfo = gre_info

data Parent
  = NoParent
  | ParentIs { par_is :: !Name }
  deriving (Eq, Data)

instance Outputable Parent where
  ppr NoParent = empty
  ppr (ParentIs n) = text "parent:" <> ppr n

instance NFData Parent where
  rnf NoParent = ()
  rnf (ParentIs n) = rnf n

plusParent :: Parent -> Parent -> Parent
plusParent p1@(ParentIs _) p2 = hasParent p1 p2
plusParent p1 p2@(ParentIs _) = hasParent p2 p1
plusParent NoParent NoParent = NoParent

hasParent :: Parent -> Parent -> Parent
hasParent p NoParent = p
hasParent p p'
  | p /= p' = pprPanic "hasParent" (ppr p <+> ppr p')
hasParent p _ = p

mkGRE :: (Name -> Maybe ImportSpec) -> GREInfo -> Parent -> Name -> GlobalRdrElt
mkGRE prov_fn info par n =
  case prov_fn n of
    Nothing -> GRE { gre_name = n
                   , gre_par = par
                   , gre_lcl = True
                   , gre_imp = emptyBag
                   , gre_info = info }
    Just is -> GRE { gre_name = n
                   , gre_par = par
                   , gre_lcl = False
                   , gre_imp = unitBag is
                   , gre_info = info }

mkExactGRE :: Name -> GREInfo -> GlobalRdrElt
mkExactGRE nm info = GRE
  { gre_name = nm, gre_par = NoParent
  , gre_lcl = False, gre_imp = emptyBag
  , gre_info = info }

mkLocalGRE :: GREInfo -> Parent -> Name -> GlobalRdrElt
mkLocalGRE = mkGRE (const Nothing)

mkLocalVanillaGRE :: Parent -> Name -> GlobalRdrElt
mkLocalVanillaGRE = mkLocalGRE Vanilla

mkLocalTyConGRE :: TyConFlavor Name -> Name -> GlobalRdrElt
mkLocalTyConGRE flav nm = mkLocalGRE (IAmTyCon flav) par nm
  where
    par = case tyConFlavorAssoc_maybe flav of
      Nothing -> NoParent
      Just p -> ParentIs p

instance HasOccName (GlobalRdrEltX info) where
  occName = greOccName

greOccName :: GlobalRdrEltX info -> OccName
greOccName (GRE { gre_name = nm }) = nameOccName nm

greDefinitionSrcSpan :: GlobalRdrEltX info -> SrcSpan
greDefinitionSrcSpan = nameSrcSpan . greName

greDefinitionModule :: GlobalRdrEltX info -> Maybe Module
greDefinitionModule = nameModule_maybe . greName

greQualModName :: Outputable info => GlobalRdrEltX info -> ModuleName
greQualModName gre@(GRE { gre_lcl = lcl, gre_imp = iss })
  | lcl, Just mod <- greDefinitionModule gre = moduleName mod
  | Just is <- headMaybe iss = is_as (is_decl is)
  | otherwise = pprPanic "greQualModName" (ppr gre)

mkParent :: Name -> AvailInfo -> Parent
mkParent _ (Avail _) = NoParent
mkParent n (AvailTC m _) | n == m = NoParent
                         | otherwise = ParentIs m

gresToNameSet :: [GlobalRdrEltX info] -> NameSet
gresToNameSet gres = foldr add emptyNameSet gres
  where
    add gre set = extendNameSet set (greName gre)

emptyGlobalRdrEnv :: GlobalRdrEnvX info
emptyGlobalRdrEnv = emptyOccEnv

globalRdrEnvElts :: GlobalRdrEnvX info -> [GlobalRdrEltX info]
globalRdrEnvElts env = nonDetFoldOccEnv (++) [] env

instance Outputable info => Outputable (GlobalRdrEltX info) where
  ppr gre = hang (ppr (greName gre) <+> ppr (gre_par gre) <+> ppr (gre_info gre))
            2 (pprNameProvenance gre)

pprGlobalRdrEnv :: Bool -> GlobalRdrEnv -> SDoc
pprGlobalRdrEnv locals_only env
  = vcat [ text "GlobalRdrEnv" <+> ppWhen locals_only (text "(locals only)")
           <+> lbrace
         , nest 2 (vcat [ pp (remove_locals gre_list) | gre_list <- nonDetOccEnvElts env ]
                   <+> rbrace)
         ]
  where
    remove_locals gres | locals_only = filter isLocalGRE gres
                       | otherwise = gres
    pp [] = empty
    pp gres@(gre:_) = hang (ppr occ <> colon) 2 (vcat (map ppr gres))
      where
        occ = nameOccName (greName gre)

data LookupGRE info where
  LookupOccName :: OccName -> WhichGREs info -> LookupGRE info
  LookupRdrName :: RdrName -> WhichGREs info -> LookupGRE info
  LookupExactName :: { lookupExactName :: Name, lookInAllNameSpaces :: Bool } -> LookupGRE info
  LookupChildren :: OccName -> LookupChild -> LookupGRE info

data WhichGREs info where
  SameNameSpace :: WhichGREs info
  RelevantGREs :: { lookupTyConsAsWell :: !Bool } -> WhichGREs GREInfo

instance Outputable (WhichGREs info) where
  ppr SameNameSpace = text "SameNameSpace"
  ppr (RelevantGREs { lookupTyConsAsWell = tcs_too })
    = braces $ hsep
      [ text "RelevantGREs"
      , if tcs_too then text "[tcs]" else empty ]

pattern AllRelevantGREs :: WhichGREs GREInfo
pattern AllRelevantGREs = RelevantGREs { lookupTyConsAsWell = True }

data LookupChild = LookupChild
  { wantedParent :: Name
  , lookupDataConFirst :: Bool
  , prioritizeParent :: Bool
  }

instance Outputable LookupChild where
  ppr (LookupChild { wantedParent = par
                   , lookupDataConFirst = dc
                   , prioritizeParent = prio_parent })
    = braces $ hsep
      [ text "LookupChild"
      , braces (text "parent:" <+> ppr par)
      , if dc then text "[dc_first]" else empty
      , if prio_parent then text "[prio_parent]" else empty
      ]

greIsRelevant :: WhichGREs GREInfo -> NameSpace -> GlobalRdrElt -> Bool
greIsRelevant which_gres ns gre
  | ns == other_ns
  = True
  | otherwise
  = case which_gres of
      SameNameSpace -> False
      RelevantGREs { lookupTyConsAsWell = tycons_too }
        | ns == varName -> tc_too
        | isDataConNameSpace ns -> tc_too
        | otherwise -> False
        where
          tc_too = tycons_too && isTcClsNameSpace other_ns
  where
    other_ns = greNameSpace gre

childGREPriority :: LookupChild -> NameSpace -> GlobalRdrEltX info -> Maybe (Int, Int)
childGREPriority (LookupChild { wantedParent = wanted_parent
                              , lookupDataConFirst = try_dc_first
                              , prioritizeParent = par_first }) ns gre =
  case child_ns_prio $ greNameSpace gre of
    Nothing -> Nothing
    Just ns_prio -> let par_prio = parent_prio $ greParent gre
                    in Just $ if par_first
                              then (par_prio, ns_prio)
                              else (ns_prio, par_prio)
  where
    child_ns_prio :: NameSpace -> Maybe Int
    child_ns_prio other_ns
      | other_ns == ns
      = Just 0
      | isTermVarNameSpace ns
      , isTermVarNameSpace other_ns
      = Just 0
      | other_ns == tcName
      = Just 1
      | ns == tcName
      , other_ns == dataName
      , try_dc_first
      = Just (-1)
      | otherwise
      = Nothing
    parent_prio :: Parent -> Int
    parent_prio (ParentIs other_parent)
      | other_parent == wanted_parent = 0
      | otherwise = 1
    parent_prio NoParent = 0

lookupGRE :: GlobalRdrEnvX info -> LookupGRE info -> [GlobalRdrEltX info]
lookupGRE env = \case
  LookupOccName occ which_gres ->
    case which_gres of
      SameNameSpace -> concat $ lookupOccEnv env occ
      rel@(RelevantGREs{}) -> filter (greIsRelevant rel (occNameSpace occ)) $
                              concat $ lookupOccEnv_AllNameSpaces env occ
  LookupRdrName rdr rel -> pickGREs rdr $ lookupGRE env (LookupOccName (rdrNameOcc rdr) rel)
  LookupExactName { lookupExactName = nm, lookInAllNameSpaces = all_ns } ->
    [ gre | gre <- lkup, greName gre == nm ]
    where
      occ = nameOccName nm
      lkup | all_ns = concat $ lookupOccEnv_AllNameSpaces env occ
           | otherwise = fromMaybe [] $ lookupOccEnv env occ
  LookupChildren occ which_child ->
    let ns = occNameSpace occ
        all_gres = concat $ lookupOccEnv_AllNameSpaces env occ
    in highestPriorityGREs (childGREPriority which_child ns) all_gres

highestPriorityGREs :: forall gre prio. Ord prio => (gre -> Maybe prio) -> [gre] -> [gre]
highestPriorityGREs priotity gres =
  take_highest_prio $ NE.group $ sort
  [ S.Arg prio gre
  | gre <- gres
  , prio <- maybeToList $ priotity gre ]
  where
    take_highest_prio :: [NE.NonEmpty (S.Arg prio gre)] -> [gre]
    take_highest_prio [] = []
    take_highest_prio (fs : _) = map (\(S.Arg _ gre) -> gre) $ NE.toList fs
{-# INLINABLE highestPriorityGREs #-}

lookupGRE_Name :: Outputable info => GlobalRdrEnvX info -> Name -> Maybe (GlobalRdrEltX info)
lookupGRE_Name env name =
  case lookupGRE env (LookupExactName { lookupExactName = name, lookInAllNameSpaces = False }) of
    [] -> Nothing
    [gre] -> Just gre
    gres -> pprPanic "lookupGRE_Name" (ppr name $$ ppr (nameOccName name) $$ ppr gres)

isLocalGRE :: GlobalRdrEltX info -> Bool
isLocalGRE (GRE { gre_lcl = lcl }) = lcl

isImportedGRE :: GlobalRdrEltX info -> Bool
isImportedGRE (GRE { gre_imp = imps }) = not $ isEmptyBag imps

pickGREs :: RdrName -> [GlobalRdrEltX info] -> [GlobalRdrEltX info]
pickGREs (Unqual{}) gres = mapMaybe pickUnqualGRE gres
pickGREs (Qual mod _) gres = mapMaybe (pickQualGRE mod) gres
pickGREs _ _ = []

pickUnqualGRE :: GlobalRdrEltX info -> Maybe (GlobalRdrEltX info)
pickUnqualGRE gre@(GRE { gre_lcl = lcl, gre_imp = iss })
  | not lcl, null iss' = Nothing
  | otherwise = Just (gre { gre_imp = iss' })
  where
    iss' = filterBag unQualSpecOK iss

pickQualGRE :: ModuleName -> GlobalRdrEltX info -> Maybe (GlobalRdrEltX info)
pickQualGRE mod gre@(GRE { gre_lcl = lcl, gre_imp = iss })
  | not lcl', null iss' = Nothing
  | otherwise = Just (gre { gre_lcl = lcl', gre_imp = iss' })
  where
    iss' = filterBag (qualSpecOK mod) iss
    lcl' = lcl && name_is_from mod

    name_is_from :: ModuleName -> Bool
    name_is_from mod = case greDefinitionModule gre of
      Just n_mod -> moduleName n_mod == mod
      Nothing -> False

plusGlobalRdrEnv :: GlobalRdrEnv -> GlobalRdrEnv -> GlobalRdrEnv
plusGlobalRdrEnv env1 env2 = plusOccEnv_C (foldr insertGRE) env1 env2

mkGlobalRdrEnv :: [GlobalRdrElt] -> GlobalRdrEnv
mkGlobalRdrEnv gres = foldr add emptyGlobalRdrEnv gres
  where
    add gre env = extendOccEnv_Acc insertGRE Utils.singleton env (greOccName gre) gre
    
insertGRE :: GlobalRdrElt -> [GlobalRdrElt] -> [GlobalRdrElt]
insertGRE new_g [] = [new_g]
insertGRE new_g (old_g : old_gs)
  | greName new_g == greName old_g
  = new_g `plusGRE` old_g : old_gs
  | otherwise
  = old_g : insertGRE new_g old_gs

plusGRE :: GlobalRdrElt -> GlobalRdrElt -> GlobalRdrElt
plusGRE g1 g2 = GRE
  { gre_name = gre_name g1
  , gre_lcl = gre_lcl g1 || gre_lcl g2
  , gre_imp = gre_imp g1 `unionBags` gre_imp g2
  , gre_par = gre_par g1 `plusParent` gre_par g2
  , gre_info = gre_info g1 `plusGREInfo` gre_info g2
  }

extendGlobalRdrEnv :: GlobalRdrEnv -> GlobalRdrElt -> GlobalRdrEnv
extendGlobalRdrEnv env gre
  = extendOccEnv_Acc insertGRE Utils.singleton env (greOccName gre) gre

greClashesWith :: GlobalRdrElt -> GlobalRdrElt -> Bool
greClashesWith new_gre old_gre = old_gre `greIsShadowed` greShadowedNameSpaces new_gre

greIsShadowed :: GlobalRdrElt -> ShadowedGREs -> Bool
greIsShadowed old_gre shadowed =
  case getUnique old_ns `namespace_is_shadowed` shadowed of
    IsShadowed -> True
    IsNotShadowed -> False
  where
    old_ns = occNameSpace $ greOccName old_gre

data IsShadowed
  = IsNotShadowed
  | IsShadowed

namespace_is_shadowed :: Unique -> ShadowedGREs -> IsShadowed
namespace_is_shadowed old_ns (ShadowedGREs shadowed_nonflds)
  | old_ns `elemUniqSet_Directly` shadowed_nonflds
  = IsShadowed
  | otherwise
  = IsNotShadowed

greShadowedNameSpaces :: GlobalRdrElt -> ShadowedGREs
greShadowedNameSpaces gre = ShadowedGREs shadowed_nonflds
  where
    ns = occNameSpace $ greOccName gre
    !shadowed_nonflds = unitUniqSet ns

data ShadowedGREs = ShadowedGREs
  { shadowedNonFieldNameSpaces :: !(UniqSet NameSpace)
  }

{- *********************************************************************
*                                                                      *
                        ImportSpec
*                                                                      *
********************************************************************* -}

data ImportSpec = ImpSpec
  { is_decl :: !ImpDeclSpec
  , is_item :: !ImpItemSpec
  }
  deriving (Eq, Data)

instance NFData ImportSpec where
  rnf = rwhnf

data ImpDeclSpec = ImpDeclSpec
  { is_mod :: !Module
  , is_as :: !ModuleName
  , is_qual :: !Bool
  , is_dloc :: !SrcSpan
  }
  deriving (Eq, Data)

data ImpItemSpec
  = ImpAll
  | ImpSome
    { is_explicit :: !Bool
    , is_iloc :: !SrcSpan
    }
  deriving (Eq, Data)

unQualSpecOK :: ImportSpec -> Bool
unQualSpecOK is = not (is_qual (is_decl is))

qualSpecOK :: ModuleName -> ImportSpec -> Bool
qualSpecOK mod is = mod == is_as (is_decl is)

importSpecLoc :: ImportSpec -> SrcSpan
importSpecLoc (ImpSpec decl ImpAll) = is_dloc decl
importSpecLoc (ImpSpec _ item) = is_iloc item

importSpecModule :: ImportSpec -> ModuleName
importSpecModule = moduleName . is_mod . is_decl

pprNameProvenance :: GlobalRdrEltX info -> SDoc
pprNameProvenance (GRE { gre_name = name, gre_lcl = lcl, gre_imp = iss })
  = ifPprDebug (vcat pp_provs) (head pp_provs)
  where
    pp_provs = pp_lcl ++ map pp_is (bagToList iss)
    pp_lcl = if lcl
             then [text "defined at" <+> ppr (nameSrcLoc name)]
             else []
    pp_is is = sep [ppr is, ppr_defn_site is name]

ppr_defn_site :: ImportSpec -> Name -> SDoc
ppr_defn_site imp_spec name
  | same_module && not (isGoodSrcSpan loc)
  = empty
  | otherwise
  = parens $ hang (text "and originally defined" <+> pp_mod) 2 (pprLoc loc)
  where
    loc = nameSrcSpan name
    defining_mod = assertPpr (isExternalName name) (ppr name) $ nameModule name
    same_module = importSpecModule imp_spec == moduleName defining_mod
    pp_mod | same_module = empty
           | otherwise = text "in" <+> quotes (ppr defining_mod)

instance Outputable ImportSpec where
  ppr imp_spec
    = text "imported" <+> qual
      <+> text "from" <+> quotes (ppr (importSpecModule imp_spec))
      <+> pprLoc (importSpecLoc imp_spec)
    where
      qual | is_qual (is_decl imp_spec) = text "qualified"
           | otherwise = empty

pprLoc :: SrcSpan -> SDoc
pprLoc (RealSrcSpan s _) = text "at" <+> ppr s
pprLoc (UnhelpfulSpan {}) = empty

opIsAt :: RdrName -> Bool
opIsAt e = e == mkUnqual varName (fsLit "@")
