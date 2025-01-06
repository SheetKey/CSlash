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

cSLASH_PRIM :: Module
cSLASH_PRIM = mkPrimModule (fsLit "CSL.Prim")

cSLASH_TYPES :: Module
cSLASH_TYPES = mkPrimModule (fsLit "CSL.Types")

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
            Known-key names
*                                                                      *
********************************************************************* -}

negateName :: Name
negateName = undefined

{- *********************************************************************
*                                                                      *
               Uniques for wired-in TyCons
*                                                                      *
********************************************************************* -}

boolTyConKey :: Unique
boolTyConKey = mkWiredInTyConUnique 4

fUNTyConKey :: Unique
fUNTyConKey = mkWiredInTyConUnique 13

{- *********************************************************************
*                                                                      *
               Uniques for wired-in DataCons
*                                                                      *
********************************************************************* -}

falseDataConKey :: Unique
falseDataConKey = mkWiredInDataConUnique 4

trueDataConKey :: Unique
trueDataConKey = mkWiredInDataConUnique 14

{- *********************************************************************
*                                                                      *
      Uniques for wired-in Ids
*                                                                      *
********************************************************************* -}

unboundKey :: Unique
unboundKey = mkWiredInMiscIdUnique 158
