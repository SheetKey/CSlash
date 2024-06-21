module CSlash.Types.Name where

import Prelude hiding ((<>))

import CSlash.Data.Maybe
import CSlash.Data.FastString
import CSlash.Types.Name.Occurrence
import CSlash.Types.SrcLoc
import CSlash.Types.TyThing
import CSlash.Types.Unique
import CSlash.Unit.Types
import CSlash.Unit.Module
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Builtin.Uniques (isTupleTyConUnique, isSumTyConUnique)

import Data.List ( intersperse )

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

data BuiltInSyntax = BuiltInSyntax | UserSyntax

nameUnique :: Name -> Unique
nameUnique name = n_uniq name

isExternalName :: Name -> Bool
isExternalName (Name {n_sort = External _}) = True
isExternalName (Name {n_sort = WiredIn _ _ _}) = True
isExternalName _ = False

nameModule :: HasDebugCallStack => Name -> Module
nameModule name =
    nameModule_maybe name `orElse`
    pprPanic "nameModule" (ppr (n_sort name) <+> ppr name)

nameModule_maybe :: Name -> Maybe Module
nameModule_maybe (Name {n_sort = External mod}) = Just mod
nameModule_maybe (Name {n_sort = WiredIn mod _ _}) = Just mod
nameModule_maybe _ = Nothing

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

nameOccName :: Name -> OccName
nameOccName name = n_occ name

cmpName :: Name -> Name -> Ordering
cmpName n1 n2 = n_uniq n1 `nonDetCmpUnique` n_uniq n2

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

instance Outputable Name where
  ppr name = pprName name

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
