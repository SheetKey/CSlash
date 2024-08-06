module CSlash.Core.ConLike where

import CSlash.Core.DataCon
import CSlash.Core.Type.Rep (Type)
import CSlash.Core.Type (mkTyConApp)
import CSlash.Types.Unique
import CSlash.Types.Name
import CSlash.Types.Name.Reader
import CSlash.Types.Basic

import CSlash.Types.GREInfo
import CSlash.Types.Var
import CSlash.Utils.Misc
import CSlash.Utils.Outputable

import Data.Maybe( isJust )
import qualified Data.Data as Data
import qualified Data.List as List


{- *********************************************************************
*                                                                      *
            Constructor-like things
*                                                                      *
********************************************************************* -}

data ConLike = RealDataCon DataCon
             | PatSynCon

{- *********************************************************************
*                                                                      *
            Instances
*                                                                      *
********************************************************************* -}

instance Eq ConLike where
  (==) = eqConLike

eqConLike :: ConLike -> ConLike -> Bool
eqConLike x y = getUnique x == getUnique y

instance Uniquable ConLike where
  getUnique (RealDataCon dc) = getUnique dc
  getUnique (PatSynCon) = panic "getUnique PatSynCon"

instance NamedThing ConLike where
  getName (RealDataCon dc) = getName dc
  getName (PatSynCon) = panic "getName PatSynCon"

instance Outputablle ConLike where
  ppr (RealDataCon dc) = ppr dc
  ppr (PatSynCon) = panic "ppr PatSynCon"

instance OutputbleBndr ConLike where
  pprInfixOcc (RealDataCon dc) = pprInfixOcc dc
  pprInfixOcc (PatSynCon) = panic "pprInfixOcc PatSynCon"
  pprPrefixOcc (RealDataCon dc) = pprPrefixOcc dc
  pprInfixOcc (PatSynCon) = panic "pprPrefixOcc PatSynCon"

instance Data.Data ConLike where
  toConstr _ = abstractConstr "ConLike"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "ConLike"
