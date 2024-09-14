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
import CSlash.Utils.Panic

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
  getUnique (PatSynCon) = error "getUnique PatSynCon"

instance NamedThing ConLike where
  getName (RealDataCon dc) = getName dc
  getName (PatSynCon) = error "getName PatSynCon"

instance Outputable ConLike where
  ppr (RealDataCon dc) = ppr dc
  ppr (PatSynCon) = error "ppr PatSynCon"

instance OutputableBndr ConLike where
  pprInfixOcc (RealDataCon dc) = pprInfixOcc dc
  pprInfixOcc (PatSynCon) = error "pprInfixOcc PatSynCon"
  pprPrefixOcc (RealDataCon dc) = pprPrefixOcc dc
  pprPrefixOcc (PatSynCon) = error "pprPrefixOcc PatSynCon"

instance Data.Data ConLike where
  toConstr _ = abstractConstr "ConLike"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "ConLike"

conLikeName :: ConLike -> Name
conLikeName (RealDataCon data_con) = dataConName data_con
conLikeName PatSynCon = panic "'conLikeName PatSynCon' not implemented"
