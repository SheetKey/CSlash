{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}

module CSlash.Types.Name
  ( Name,
    BuiltInSyntax(..),
    mkSystemName, mkSystemNameAt,
    mkInternalName, mkClonedInternalName, mkDerivedInternalName,
    mkSystemVarName, mkSysTvName,
    mkFCallName,
    mkExternalName, mkWiredInName,
    
    nameUnique, setNameUnique,
    nameOccName, nameNameSpace, nameModule, nameModule_maybe,
    setNameLoc,
    tidyNameOcc,
    localiseName,
    namePun_maybe,

    pprName,
    nameSrcLoc, nameSrcSpan, pprNameDefnLoc, pprDefinedAt,
    pprFullName, pprTickyName,

    isSystemName, isInternalName, isExternalName,
    isTyVarName, isTyConName,
    -- isDataConName,
    isValName, isVarName,
    -- isDynLinkName, isFieldName,
    isWiredInName, isWiredIn, isBuiltInSyntax, isTupleTyConName,
    isSumTyConName,
    -- isUnboxedTupleDataConLikeName,
    isHoleName,
    wiredInNameTyThing_maybe,
    nameIsLocalOrFrom, nameIsExternalOrFrom, nameIsHomePackage,
    nameIsHomePackageImport, nameIsFromExternalPackage,
    stableNameCmp,

    NamedThing(..),
    getSrcLoc, getSrcSpan, getOccString, getOccFS,

    pprInfixName, pprPrefixName, pprModulePrefix, pprNameUnqualified,
    nameStableString,

    module CSlash.Types.Name.Occurrence
) where

import Prelude hiding ((<>))

import CSlash.Data.Maybe
import CSlash.Data.FastString
import CSlash.Types.Name.Occurrence
import CSlash.Types.SrcLoc
import CSlash.Types.TyThing
import CSlash.Types.Unique
import CSlash.Unit.Home
import CSlash.Unit.Types
import CSlash.Unit.Module
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Binary
import CSlash.Builtin.Uniques (isTupleTyConUnique, isSumTyConUnique)

import Data.List ( intersperse )

import Control.DeepSeq
import Data.Data
import qualified Data.Semigroup as S

data Name = Name
  { n_sort :: NameSort
  , n_occ :: OccName
  , n_uniq :: {-# UNPACK #-} !Unique
  , n_loc :: !SrcSpan
  }

data NameSort
  = External Module
  | WiredIn Module TyThing BuiltInSyntax
  | Internal
  | System

instance Outputable NameSort where
  ppr (External _) = text "external"
  ppr (WiredIn _ _ _) = text "wired-in"
  ppr Internal = text "internal"
  ppr System = text "system"

instance NFData Name where
  rnf Name{..} = rnf n_sort `seq` rnf n_occ `seq` n_uniq `seq` rnf n_loc

instance NFData NameSort where
  rnf (External m) = rnf m
  rnf (WiredIn m t b) = rnf m `seq` t `seq` b `seq` ()
  rnf Internal = ()
  rnf System = ()

data BuiltInSyntax = BuiltInSyntax | UserSyntax

instance HasOccName Name where
  occName = nameOccName

nameUnique :: Name -> Unique
nameUnique name = n_uniq name

nameOccName :: Name -> OccName
nameOccName name = n_occ name

nameNameSpace :: Name -> NameSpace
nameNameSpace name = occNameSpace (n_occ name)

nameSrcLoc :: Name -> SrcLoc
nameSrcLoc name = srcSpanStart (n_loc name)

nameSrcSpan :: Name -> SrcSpan
nameSrcSpan name = n_loc name

isInternalName :: Name -> Bool
isInternalName name = not (isExternalName name)

isExternalName :: Name -> Bool
isExternalName (Name {n_sort = External _}) = True
isExternalName (Name {n_sort = WiredIn _ _ _}) = True
isExternalName _ = False

isSystemName :: Name -> Bool
isSystemName (Name {n_sort = System}) = True
isSystemName _                        = False

isWiredInName :: Name -> Bool
isWiredInName (Name {n_sort = WiredIn _ _ _}) = True
isWiredInName _ = False

isWiredIn :: NamedThing thing => thing -> Bool
isWiredIn = isWiredInName . getName

wiredInNameTyThing_maybe :: Name -> Maybe TyThing
wiredInNameTyThing_maybe (Name {n_sort = WiredIn _ thing _}) = Just thing
wiredInNameTyThing_maybe _ = Nothing

isBuiltInSyntax :: Name -> Bool
isBuiltInSyntax (Name {n_sort = WiredIn _ _ BuiltInSyntax}) = True
isBuiltInSyntax _                                           = False

isTupleTyConName :: Name -> Bool
isTupleTyConName = isJust . isTupleTyConUnique . getUnique

isSumTyConName :: Name -> Bool
isSumTyConName = isJust . isSumTyConUnique . getUnique

isHoleName :: Name -> Bool
isHoleName = isHoleModule . nameModule

nameModule :: HasDebugCallStack => Name -> Module
nameModule name =
    nameModule_maybe name `orElse`
    pprPanic "nameModule" (ppr (n_sort name) <+> ppr name)

nameModule_maybe :: Name -> Maybe Module
nameModule_maybe (Name {n_sort = External mod}) = Just mod
nameModule_maybe (Name {n_sort = WiredIn mod _ _}) = Just mod
nameModule_maybe _ = Nothing

is_from :: Module -> Module -> Bool
is_from from mod = from == mod

namePun_maybe :: Name -> Maybe FastString
namePun_maybe name
  | Just ar <- isTupleTyConUnique (getUnique name)
  , ar /= 1 =
    Just (fsLit $ "(" ++ commas ar ++ ")")
  | Just ar <- isSumTyConUnique (getUnique name)
  = Just (fsLit $ "( " ++ bars ar ++ " )")
  where
    commas ar = replicate (ar-1) ','
    bars ar = intersperse ' ' (replicate (ar-1) '|')
namePun_maybe _ = Nothing    

nameIsLocalOrFrom :: Module -> Name -> Bool
nameIsLocalOrFrom from name
  | Just mod <- nameModule_maybe name = is_from from mod
  | otherwise                         = True

nameIsExternalOrFrom :: Module -> Name -> Bool
nameIsExternalOrFrom from name
  | Just mod <- nameModule_maybe name = is_from from mod
  | otherwise                         = False

nameIsHomePackage :: Module -> Name -> Bool
nameIsHomePackage this_mod
  = \nm -> case n_sort nm of
              External nm_mod    -> moduleUnit nm_mod == this_pkg
              WiredIn nm_mod _ _ -> moduleUnit nm_mod == this_pkg
              Internal -> True
              System   -> False
  where
    this_pkg = moduleUnit this_mod  

nameIsHomePackageImport :: Module -> Name -> Bool
nameIsHomePackageImport this_mod
  = \nm -> case nameModule_maybe nm of
              Nothing -> False
              Just nm_mod -> nm_mod /= this_mod
                          && moduleUnit nm_mod == this_pkg
  where
    this_pkg = moduleUnit this_mod

nameIsFromExternalPackage :: HomeUnit -> Name -> Bool
nameIsFromExternalPackage home_unit name
  | Just mod <- nameModule_maybe name
  , notHomeModule home_unit mod
  = True
  | otherwise
  = False

isTyVarName :: Name -> Bool
isTyVarName name = isTvOcc (nameOccName name)

isKdVarName :: Name -> Bool
isKdVarName name = isKvOcc (nameOccName name)

isTyConName :: Name -> Bool
isTyConName name = isTcOcc (nameOccName name)

-- isDataConName :: Name -> Bool
-- isDataConName name = isDataOcc (nameOccName name)

isValName :: Name -> Bool
isValName name = isValOcc (nameOccName name)

isVarName :: Name -> Bool
isVarName = isVarOcc . nameOccName

mkInternalName :: Unique -> OccName -> SrcSpan -> Name
mkInternalName uniq occ loc = Name { n_uniq = uniq
                                   , n_sort = Internal
                                   , n_occ = occ
                                   , n_loc = loc }

mkClonedInternalName :: Unique -> Name -> Name
mkClonedInternalName uniq (Name { n_occ = occ, n_loc = loc })
  = Name { n_uniq = uniq, n_sort = Internal
         , n_occ = occ, n_loc = loc }

mkDerivedInternalName :: (OccName -> OccName) -> Unique -> Name -> Name
mkDerivedInternalName derive_occ uniq (Name { n_occ = occ, n_loc = loc })
  = Name { n_uniq = uniq, n_sort = Internal
         , n_occ = derive_occ occ, n_loc = loc }

mkExternalName :: Unique -> Module -> OccName -> SrcSpan -> Name
{-# INLINE mkExternalName #-}
mkExternalName uniq mod occ loc
  = Name { n_uniq = uniq, n_sort = External mod,
           n_occ = occ, n_loc = loc }

mkWiredInName :: Module -> OccName -> Unique -> TyThing -> BuiltInSyntax -> Name
{-# INLINE mkWiredInName #-}
mkWiredInName mod occ uniq thing built_in
  = Name { n_uniq = uniq,
           n_sort = WiredIn mod thing built_in,
           n_occ = occ, n_loc = wiredInSrcSpan }

mkSystemName :: Unique -> OccName -> Name
mkSystemName uniq occ = mkSystemNameAt uniq occ noSrcSpan

mkSystemNameAt :: Unique -> OccName -> SrcSpan -> Name
mkSystemNameAt uniq occ loc = Name { n_uniq = uniq, n_sort = System
                                   , n_occ = occ, n_loc = loc }

mkSystemVarName :: Unique -> FastString -> Name
mkSystemVarName uniq fs = mkSystemName uniq (mkVarOccFS fs)

mkSysTvName :: Unique -> FastString -> Name
mkSysTvName uniq fs = mkSystemName uniq (mkTyVarOccFS fs)

mkFCallName :: Unique -> FastString -> Name
mkFCallName uniq str = mkInternalName uniq (mkVarOccFS str) noSrcSpan

setNameUnique :: Name -> Unique -> Name
setNameUnique name uniq = name {n_uniq = uniq}


setNameLoc :: Name -> SrcSpan -> Name
setNameLoc name loc = name {n_loc = loc}

tidyNameOcc :: Name -> OccName -> Name
tidyNameOcc name@(Name { n_sort = System }) occ = name { n_occ = occ, n_sort = Internal}
tidyNameOcc name                            occ = name { n_occ = occ }

localiseName :: Name -> Name
localiseName n = n { n_sort = Internal }

cmpName :: Name -> Name -> Ordering
cmpName n1 n2 = n_uniq n1 `nonDetCmpUnique` n_uniq n2

stableNameCmp :: Name -> Name -> Ordering
stableNameCmp (Name { n_sort = s1, n_occ = occ1 })
              (Name { n_sort = s2, n_occ = occ2 })
  = sort_cmp s1 s2 S.<> compare occ1 occ2
    -- The ordinary compare on OccNames is lexicographic
  where
    -- Later constructors are bigger
    sort_cmp (External m1) (External m2)       = m1 `stableModuleCmp` m2
    sort_cmp (External {}) _                   = LT
    sort_cmp (WiredIn {}) (External {})        = GT
    sort_cmp (WiredIn m1 _ _) (WiredIn m2 _ _) = m1 `stableModuleCmp` m2
    sort_cmp (WiredIn {})     _                = LT
    sort_cmp Internal         (External {})    = GT
    sort_cmp Internal         (WiredIn {})     = GT
    sort_cmp Internal         Internal         = EQ
    sort_cmp Internal         System           = LT
    sort_cmp System           System           = EQ
    sort_cmp System           _                = GT

instance Eq Name where
  a == b = case (a `compare` b) of
             EQ -> True
             _ -> False
  a /= b = case (a `compare` b) of
             EQ -> False
             _ -> True

instance Ord Name where
  compare = cmpName

instance Uniquable Name where
  getUnique = nameUnique

instance NamedThing Name where
  getName n = n

instance Data Name where
  toConstr _ = abstractConstr "Name"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "Name"

instance Binary Name where
  put_ bh name =
    case getUserData bh of
      UserData { ud_put_nonbinding_name = put_name } -> put_name bh name

  get bh =
    case getUserData bh of
      UserData { ud_get_name = get_name } -> get_name bh

instance Outputable Name where
  ppr name = pprName name

instance OutputableBndr Name where
  pprBndr _ name = pprName name
  pprInfixOcc  = pprInfixName
  pprPrefixOcc = pprPrefixName

pprName :: IsLine doc => Name -> doc
pprName name@(Name {n_sort = sort, n_uniq = uniq, n_occ = occ})
  = docWithStyle codeDoc normalDoc
  where
    codeDoc = case sort of
                WiredIn mod _ _ -> pprModule mod <> char '_' <> z_occ
                External mod -> pprModule mod <> char '_' <> z_occ
                System -> pprUniqueAlways uniq
                Internal -> pprUniqueAlways uniq
    z_occ = ztext $ zEncodeFS $ occNameMangledFS occ
    normalDoc sty =
      getPprDebug $ \ debug ->
      sdocOption sdocListTuplePuns $ \ listTuplePuns ->
        handlePuns listTuplePuns (namePun_maybe name) $
        case sort of
          WiredIn mod _ builtin -> pprExternal debug sty uniq mod occ True builtin
          External mod -> pprExternal debug sty uniq mod occ False UserSyntax
          System -> pprSystem debug sty uniq occ
          Internal -> pprInternal debug sty uniq occ
    handlePuns :: Bool -> Maybe FastString -> SDoc -> SDoc
    handlePuns True (Just pun) _ = ftext pun
    handlePuns _ _ r = r
{-# SPECIALIZE pprName :: Name -> SDoc #-}
{-# SPECIALIZE pprName :: Name -> HLine #-}

pprFullName :: Module -> Name -> SDoc
pprFullName this_mod Name{n_sort = sort, n_uniq = uniq, n_occ = occ} =
  let mod = case sort of
        WiredIn  m _ _ -> m
        External m     -> m
        System         -> this_mod
        Internal       -> this_mod
      in ftext (unitIdFS (moduleUnitId mod))
         <> colon    <> ftext (moduleNameFS $ moduleName mod)
         <> dot      <> ftext (occNameFS occ)
         <> char '_' <> pprUniqueAlways uniq

pprTickyName :: Module -> Name -> SDoc
pprTickyName this_mod name
  | isInternalName name = pprName name <+> parens (ppr this_mod)
  | otherwise           = pprName name

pprNameUnqualified :: Name -> SDoc
pprNameUnqualified Name { n_occ = occ } = ppr_occ_name occ

pprExternal
  :: Bool
  -> PprStyle
  -> Unique
  -> Module
  -> OccName
  -> Bool
  -> BuiltInSyntax
  -> SDoc
pprExternal debug sty uniq mod occ is_wired is_builtin
  | debug = pp_mod <> ppr_occ_name occ
            <> braces (hsep [ if is_wired then text "(w)" else empty
                            , pprNameSpaceBrief (occNameSpace occ)
                            , pprUnique uniq
                            ])
  | BuiltInSyntax <- is_builtin = ppr_occ_name occ
  | otherwise = if isHoleModule mod
                then case qualName sty mod occ of
                       NameUnqual -> ppr_occ_name occ
                       _ -> braces
                         (pprModuleName (moduleName mod) <> dot <> ppr_occ_name occ)
                else pprModulePrefix sty mod occ <> ppr_occ_name occ
  where
    pp_mod = ppUnlessOption sdocSuppressModulePrefixes
             (pprModule mod <> dot)

pprInternal :: Bool -> PprStyle -> Unique -> OccName -> SDoc
pprInternal debug sty uniq occ
  | debug = ppr_occ_name occ <> braces (hsep [ pprNameSpaceBrief (occNameSpace occ)
                                             , pprUnique uniq
                                             ])
  | dumpStyle sty = ppr_occ_name occ <> ppr_underscore_unique uniq
  | otherwise = ppr_occ_name occ

pprSystem :: Bool -> PprStyle -> Unique -> OccName -> SDoc
pprSystem debug _sty uniq occ
  | debug = ppr_occ_name occ <> ppr_underscore_unique uniq
            <> braces (pprNameSpaceBrief (occNameSpace occ))
  | otherwise = ppr_occ_name occ <> ppr_underscore_unique uniq

pprModulePrefix :: PprStyle -> Module -> OccName -> SDoc
pprModulePrefix sty mod occ = ppUnlessOption sdocSuppressModulePrefixes $
  case qualName sty mod occ of
    NameQual modname -> pprModuleName modname <> dot
    NameNotInScope1 -> pprModule mod <> dot
    NameNotInScope2 -> pprUnit (moduleUnit mod) <> colon
                       <> pprModuleName (moduleName mod) <> dot
    NameUnqual -> empty

pprUnique :: Unique -> SDoc
pprUnique uniq
  = ppUnlessOption sdocSuppressUniques $
      pprUniqueAlways uniq

ppr_underscore_unique :: Unique -> SDoc
ppr_underscore_unique uniq
  = ppUnlessOption sdocSuppressUniques $
      char '_' <> pprUniqueAlways uniq

ppr_occ_name :: OccName -> SDoc
ppr_occ_name occ = ftext (occNameFS occ)

pprDefinedAt :: Name -> SDoc
pprDefinedAt name = text "Defined" <+> pprNameDefnLoc name

pprNameDefnLoc :: Name -> SDoc
pprNameDefnLoc name
  = case nameSrcLoc name of
       RealSrcLoc s _ -> text "at" <+> ppr s
       UnhelpfulLoc s
         | isInternalName name || isSystemName name
         -> text "at" <+> ftext s
         | otherwise
         -> text "in" <+> quotes (ppr (nameModule name))

nameStableString :: Name -> String
nameStableString Name{..} =
  nameSortStableString n_sort ++ "$" ++ occNameString n_occ

nameSortStableString :: NameSort -> String
nameSortStableString System = "$_sys"
nameSortStableString Internal = "$_in"
nameSortStableString (External mod) = moduleStableString mod
nameSortStableString (WiredIn mod _ _) = moduleStableString mod

class NamedThing a where
    getOccName :: a -> OccName
    getName    :: a -> Name

    getOccName n = nameOccName (getName n)

instance NamedThing e => NamedThing (Located e) where
    getName = getName . unLoc

getSrcLoc           :: NamedThing a => a -> SrcLoc
getSrcSpan          :: NamedThing a => a -> SrcSpan
getOccString        :: NamedThing a => a -> String
getOccFS            :: NamedThing a => a -> FastString

getSrcLoc           = nameSrcLoc           . getName
getSrcSpan          = nameSrcSpan          . getName
getOccString        = occNameString        . getOccName
getOccFS            = occNameFS            . getOccName

pprInfixName :: (Outputable a, NamedThing a) => a -> SDoc
pprInfixName  n = pprInfixVar (isSymOcc (getOccName n)) (ppr n)

pprPrefixName :: NamedThing a => a -> SDoc
pprPrefixName thing = pprPrefixVar (isSymOcc (nameOccName name)) (ppr name)
 where
   name = getName thing
