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

data ConLike tv kv
  = RealDataCon (DataCon tv kv)
  | PatSynCon

{- *********************************************************************
*                                                                      *
            Instances
*                                                                      *
********************************************************************* -}

instance Eq (ConLike tv kv) where
  (==) = eqConLike

eqConLike :: ConLike tv kv -> ConLike tv kv -> Bool
eqConLike x y = getUnique x == getUnique y

instance Uniquable (ConLike tv kv) where
  getUnique (RealDataCon dc) = getUnique dc
  getUnique (PatSynCon) = error "getUnique PatSynCon"

instance NamedThing (ConLike tv kv) where
  getName (RealDataCon dc) = getName dc
  getName (PatSynCon) = error "getName PatSynCon"

instance Outputable (ConLike tv kv) where
  ppr (RealDataCon dc) = ppr dc
  ppr (PatSynCon) = error "ppr PatSynCon"

instance OutputableBndr (ConLike tv kv) where
  pprInfixOcc (RealDataCon dc) = pprInfixOcc dc
  pprInfixOcc (PatSynCon) = error "pprInfixOcc PatSynCon"
  pprPrefixOcc (RealDataCon dc) = pprPrefixOcc dc
  pprPrefixOcc (PatSynCon) = error "pprPrefixOcc PatSynCon"

instance (Data.Typeable tv, Data.Typeable kv) => Data.Data (ConLike tv kv) where
  toConstr _ = abstractConstr "ConLike"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "ConLike"

conLikeArity :: ConLike tv kv -> Arity
conLikeArity (RealDataCon data_con) = dataConArity data_con
conLikeArity PatSynCon = panic "conLikeArity PatSynCon"

conLikeConInfo :: ConLike tv kv -> ConInfo
conLikeConInfo con = mkConInfo (conLikeArity con)

conLikeName :: ConLike tv kv -> Name
conLikeName (RealDataCon data_con) = dataConName data_con
conLikeName PatSynCon = panic "'conLikeName PatSynCon' not implemented"
