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

import CSlash.Rename.Unbound

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

lookupFixityRn :: Name -> RnM Fixity
lookupFixityRn = fmap snd . lookupFixityRn_help

lookupFixityRn_help :: Name -> RnM (Bool, Fixity)
lookupFixityRn_help name
  | isUnboundName name
  = return (False, Fixity minPrecedence InfixL)
  | otherwise
  = do local_fix_env <- getFixityEnv
       case lookupNameEnv local_fix_env name of
         Just (FixItem _ fix) -> return (True, fix)
         Nothing -> do this_mod <- getModule
                       if nameIsLocalOrFrom this_mod name
                         then return (False, defaultFixity)
                         else lookup_imported
  where
    occ = nameOccName name
    lookup_imported = do
      iface <- loadInterfaceForName doc name
      let mb_fix = mi_fix_fn (mi_final_exts iface) occ
          msg = case mb_fix of
                  Nothing -> text "looking up name" <+> ppr name
                             <+> text "in iface, but found no fixity for it."
                             <+> text "Using default fixity instead."
                  Just f -> text "looking up name in iface and found:"
                            <+> vcat [ppr name, ppr f]
      traceRn "lookupFixityRn_either:" msg
      return $ maybe (False, defaultFixity) (\f -> (True, f)) mb_fix

    doc = text "Checking fixity for" <+> ppr name

lookupTyFixityRn :: LocatedN Name -> RnM Fixity
lookupTyFixityRn = lookupFixityRn . unLoc
