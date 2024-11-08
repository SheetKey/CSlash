{-# LANGUAGE NamedFieldPuns #-}

module CSlash.Rename.Fixity where

import CSlash.Iface.Load
import CSlash.Cs
import CSlash.Tc.Utils.Monad

import CSlash.Unit.Module
import CSlash.Unit.Module.ModIface

import CSlash.Types.Fixity.Env
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Fixity
import CSlash.Types.SourceText
import CSlash.Types.SrcLoc

import CSlash.Utils.Outputable

import CSlash.Data.Maybe

-- import CSlash.Rename.Unbound

{- *****************************************************
*                                                      *
                Fixities
*                                                      *
***************************************************** -}

data MiniFixityEnv = MFE
  { mfe_data_level_names :: FastStringEnv (Located Fixity)
  , mfe_type_level_names :: FastStringEnv (Located Fixity)
  }

addLocalFixities :: MiniFixityEnv -> [Name] -> RnM a -> RnM a
addLocalFixities env names thing_inside = extendFixityEnv (mapMaybe find_fixity names) thing_inside
  where
    find_fixity name = case lookupMiniFixityEnv env name of
                         Just lfix -> Just (name, FixItem occ (unLoc lfix))
                         Nothing -> Nothing
      where
        occ = nameOccName name

lookupMiniFixityEnv :: MiniFixityEnv -> Name -> Maybe (Located Fixity)
lookupMiniFixityEnv MFE { mfe_data_level_names, mfe_type_level_names } name
  | isValNameSpace namespace = find_fixity_in_env mfe_data_level_names name
  | otherwise = find_fixity_in_env mfe_type_level_names name
  where
    namespace = nameNameSpace name

    find_fixity_in_env mini_fix_env name = lookupFsEnv mini_fix_env (occNameFS occ)
      where
        occ = nameOccName name

emptyMiniFixityEnv :: MiniFixityEnv
emptyMiniFixityEnv = MFE emptyFsEnv emptyFsEnv
