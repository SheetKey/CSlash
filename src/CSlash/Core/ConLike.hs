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

data ConLike p
  = RealDataCon (DataCon p)
  | PatSynCon

{- *********************************************************************
*                                                                      *
            Instances
*                                                                      *
********************************************************************* -}

instance Eq (ConLike p) where
  (==) = eqConLike

eqConLike :: ConLike p -> ConLike p -> Bool
eqConLike x y = getUnique x == getUnique y

instance Uniquable (ConLike p) where
  getUnique (RealDataCon dc) = getUnique dc
  getUnique (PatSynCon) = error "getUnique PatSynCon"

instance NamedThing (ConLike p) where
  getName (RealDataCon dc) = getName dc
  getName (PatSynCon) = error "getName PatSynCon"

instance Outputable (ConLike p) where
  ppr (RealDataCon dc) = ppr dc
  ppr (PatSynCon) = error "ppr PatSynCon"

instance OutputableBndr (ConLike p) where
  pprInfixOcc (RealDataCon dc) = pprInfixOcc dc
  pprInfixOcc (PatSynCon) = error "pprInfixOcc PatSynCon"
  pprPrefixOcc (RealDataCon dc) = pprPrefixOcc dc
  pprPrefixOcc (PatSynCon) = error "pprPrefixOcc PatSynCon"

instance Data.Typeable p => Data.Data (ConLike p) where
  toConstr _ = abstractConstr "ConLike"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "ConLike"

conLikeArity :: ConLike p -> Arity
conLikeArity (RealDataCon data_con) = dataConArity data_con
conLikeArity PatSynCon = panic "conLikeArity PatSynCon"

conLikeConInfo :: ConLike p -> ConInfo
conLikeConInfo con = mkConInfo (conLikeArity con)

conLikeName :: ConLike p -> Name
conLikeName (RealDataCon data_con) = dataConName data_con
conLikeName PatSynCon = panic "'conLikeName PatSynCon' not implemented"
