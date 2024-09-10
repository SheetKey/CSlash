module CSlash.Types.Fixity.Env where

import CSlash.Types.Fixity
import CSlash.Types.Name
import CSlash.Types.Name.Env

import CSlash.Utils.Outputable

type FixityEnv = NameEnv FixItem

data FixItem = FixItem OccName Fixity

instance Outputable FixItem where
  ppr (FixItem occ fix) = ppr fix <+> ppr occ

emptyFixityEnv :: FixitEnv
emptyFixityEnv = emptyNameEnv

lookupFixity :: FixityEnv -> Name -> Fixity
lookupFixity env n = case lookupNameEnv env n of
                       Just (FixItem _ fix) -> fix
                       Nothing -> defaultFixity