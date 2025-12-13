module CSlash.Builtin.Names
  ( Unique, Uniquable(..), hasKey,
    module CSlash.Builtin.Names
  ) where

import CSlash.Unit.Types
import CSlash.Types.Name.Occurrence
import CSlash.Types.Name.Reader
import CSlash.Types.Unique
import CSlash.Builtin.Uniques
import CSlash.Types.Name
import CSlash.Types.SrcLoc
import CSlash.Data.FastString
import CSlash.Data.List.Infinite (Infinite (..))
import qualified CSlash.Data.List.Infinite as Inf

import CSlash.Language.Syntax.Module.Name

import CSlash.Utils.Panic

{- *********************************************************************
*                                                                      *
     allNameStrings
*                                                                      *
********************************************************************* -}

allNameStrings :: Infinite String
-- Infinite list of a,b,c...z, aa, ab, ac, ... etc
allNameStrings = Inf.allListsOf ['a'..'z']

allNameStringList :: [String]
-- Infinite list of a,b,c...z, aa, ab, ac, ... etc
allNameStringList = Inf.toList allNameStrings

{- *********************************************************************
*                                                                      *
      Local names
*                                                                      *
********************************************************************* -}

mkUnboundName :: OccName -> Name
mkUnboundName occ = mkInternalName unboundKey occ noSrcSpan

isUnboundName :: Name -> Bool
isUnboundName name = name `hasKey` unboundKey

{- *********************************************************************
*                                                                      *
      Known key Names
*                                                                      *
********************************************************************* -}

basicKnownKeyNames :: [Name]
basicKnownKeyNames
  = []

{- *********************************************************************
*                                                                      *
      Module names
*                                                                      *
********************************************************************* -}

cSLASH_BUILTIN :: Module
cSLASH_BUILTIN = mkPrimModule (fsLit "CSL.BuiltIn")

rOOT_MAIN :: Module
rOOT_MAIN= mkMainModule (fsLit ":Main")

pRELUDE_NAME :: ModuleName
pRELUDE_NAME = mkModuleNameFS (fsLit "Prelude")

mAIN_NAME :: ModuleName
mAIN_NAME = mkModuleNameFS (fsLit "Main")

mkPrimModule :: FastString -> Module
mkPrimModule m = mkModule primUnit (mkModuleNameFS m)

mkMainModule :: FastString -> Module
mkMainModule m = mkModule mainUnit (mkModuleNameFS m)

{- *********************************************************************
*                                                                      *
            RdrNames
*                                                                      *
********************************************************************* -}

main_RDR_Unqual :: RdrName
main_RDR_Unqual = mkUnqual varName (fsLit "main")

{- *********************************************************************
*                                                                      *
            Known-key names
*                                                                      *
********************************************************************* -}

negateName :: Name
negateName = panic "negateName"

{- *********************************************************************
*                                                                      *
               Local helpers
*                                                                      *
********************************************************************* -}

tcQual :: Module -> FastString -> Unique -> Name
{-# INLINE tcQual #-}
tcQual modu str unique = mk_known_key_name tcName modu str unique

mk_known_key_name :: NameSpace -> Module -> FastString -> Unique -> Name
{-# INLINE mk_known_key_name #-}
mk_known_key_name space modu str unique
  = mkExternalName unique modu (mkOccNameFS space str) noSrcSpan

{- *********************************************************************
*                                                                      *
               Uniques for wired-in TyCons
*                                                                      *
********************************************************************* -}

boolTyConKey :: Unique
boolTyConKey = mkWiredInTyConUnique 4

fUNTyConKey :: Unique
fUNTyConKey = mkWiredInTyConUnique 13

realWorldTyConKey :: Unique
realWorldTyConKey = mkWiredInTyConUnique 37

eqTyConKey :: Unique
eqTyConKey = mkWiredInTyConUnique 53

ioResTyConKey :: Unique
ioResTyConKey = mkWiredInTyConUnique 55

primIoTyConKey :: Unique
primIoTyConKey = mkWiredInTyConUnique 56

ioTyConKey :: Unique
ioTyConKey = mkWiredInTyConUnique 57

{- *********************************************************************
*                                                                      *
               Uniques for wired-in DataCons
*                                                                      *
********************************************************************* -}

falseDataConKey :: Unique
falseDataConKey = mkWiredInDataConUnique 4

trueDataConKey :: Unique
trueDataConKey = mkWiredInDataConUnique 14

mkIoDataConKey :: Unique
mkIoDataConKey = mkWiredInDataConUnique 16

mkIoResDataConKey :: Unique
mkIoResDataConKey = mkWiredInDataConUnique 17

{- *********************************************************************
*                                                                      *
      Uniques for wired-in Ids
*                                                                      *
********************************************************************* -}

assertIdKey :: Unique 
assertIdKey = mkWiredInMiscIdUnique 44

unboundKey :: Unique
unboundKey = mkWiredInMiscIdUnique 158
