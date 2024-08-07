module CSlash.Core.DataCon where

import CSlash.Language.Syntax.Basic
import CSlash.Language.Syntax.Module.Name

import CSlash.Core.Type as Type
import CSlash.Core.TyCon
import {-# SOURCE #-} CSlash.Types.TyThing
import CSlash.Types.SourceText
import CSlash.Types.Name
import CSlash.Builtin.Names
import CSlash.Types.Var
import CSlash.Types.Basic
import CSlash.Data.FastString
import CSlash.Unit.Types
import CSlash.Utils.Binary
import CSlash.Types.Unique.FM ( UniqFM )
import CSlash.Types.Unique.Set

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic

import Data.ByteString (ByteString)
import qualified Data.ByteString.Builder as BSB
import qualified Data.ByteString.Lazy    as LBS
import qualified Data.Data as Data
import Data.Char
import Data.List( find )
import Numeric (showInt)

{- *********************************************************************
*                                                                      *
            Data constructors
*                                                                      *
********************************************************************* -}

-- NOTE:
-- If I add first class existentials
-- (i.e., pack/open or pack/unpack)
-- then I dot need (or want)
-- to have existentials in datacons.
-- INSTEAD:
-- we should have (invariant) length dcUnivTyVars <= length dcArgTys == length tyConBinders
-- '<=' since in GADTS, some tyvars in the datacon may be instantiated.

data DataCon = MkData
  { dcName :: Name
  , dcUnique :: Unique
  , dcTag :: ConTag
  , dcUnivTyVars :: [TypeVar]
  , dcWorkId :: Id
  , dcArity :: Arity -- dcRepArity
  , dcTyCon :: TyCon -- dcRepTyCon
  , dcArgTys :: [Type]
  , dcResTy :: Type
  , dcType :: Type   -- This is the worker type (dcRepType in GHC, but we have no wrappers)
  , dcInfix :: Bool
  }

{- *********************************************************************
*                                                                      *
            Instances
*                                                                      *
********************************************************************* -}

instance Eq DataCon where
  a == b = getUnique a == getUnique b
  a /= b = getUnique a /= getUnique b

instance Uniquable DataCon where
  getUnique = dcUnique

instance NamedThing DataCon where
  getName = dcName

instance Outputable DataCon where
  ppr con = ppr (dataConName con)

instance OutputableBndr DataCon where
  pprInfixOcc con = pprInfixName (dataConName con)
  pprPrefixOcc con = pprPrefixName (dataConName con)

instance Data.Data DataCon where
  toConstr _   = abstractConstr "DataCon"
  gunfold _ _  = error "gunfold"
  dataTypeOf _ = mkNoRepType "DataCon"

{- *********************************************************************
*                                                                      *
            Construction
*                                                                      *
********************************************************************* -}

mkDataCon
  :: Name
  -> Bool
  -> [TypeVar]
  -> [KnotTied Type]
  -> KnotTied Type
  -> KnotTied TyCon
  -> ConTag
  -> Id
  -> DataCon
mkDataCon name declared_infix univ_tvs arg_tys res_type tycon tag work_id
  = con
  where
    con = MkData { dcName = name
                 , dcUnique = nameUnique name
                 , dcInfix = declared_infix
                 , dcUnivTyVars = univ_tvs
                 , dcArgTys = arg_tys
                 , dcResTy = res_type
                 , dcTyCon = tycon
                 , dcTag = tag
                 , dcType = dataConType con
                 , dcWorkId = work_id
                 , dcArity = length arg_tys
                 }

dataConName :: DataCon -> Name
dataConName = dcName
         
dataConArity :: DataCon -> Arity
dataConArity (MkData { dcArity = arity }) = arity

dataConWorkId :: DataCon -> Id
dataConWorkId dc = dcWorkId dc

-- must change if I allow existentials in data type declarations (WHICH I SHOULD NOT DO!!!)
dataConFullSig :: DataCon -> ([TypeVar],[Type], Type)
dataConFullSig (MkData { dcUnivTyVars = univ_tvs
                       , dcArgTys = arg_tys
                       , dcType = full_ty })
  = (univ_tvs, arg_tys, full_ty)

-- dataConWrapperType in GHC
-- This may need to change:
-- since we have no wrappers, the worker type is the dcType.
-- So we should be able to take the varType from the dcWorkId.
-- We should validate this when we get to implementing checkValidDataCon.
dataConType :: DataCon -> Type
dataConType (MkData { dcWorkId = var }) = varType var
