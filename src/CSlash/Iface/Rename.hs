{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiWayIf #-}

module CSlash.Iface.Rename where

import CSlash.Driver.Env

import CSlash.Tc.Utils.Monad

import CSlash.Iface.Syntax
import CSlash.Iface.Env
-- import {-# SOURCE #-} GHC.Iface.Load -- a bit vexing

import CSlash.Unit
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.Deps

import CSlash.Tc.Errors.Types
import CSlash.Types.SrcLoc
import CSlash.Types.Unique.FM
import CSlash.Types.Avail
import CSlash.Types.Error
import CSlash.Types.Var
import CSlash.Types.Basic
import CSlash.Types.Name
-- import CSlash.Types.Name.Shape

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Error
import CSlash.Utils.Fingerprint
import CSlash.Utils.Panic

import qualified Data.Traversable as T

import Data.IORef
import Data.Function ((&))

rnModIface
  :: CsEnv
  -> [(ModuleName, Module)]
  -> Maybe NameShape
  -> ModIface
  -> IO (Either (Messages TcRnMessage) ModIface)
rnModIface cs_env insts nsubst iface = initRnIface cs_env iface insts nsubst $ do
  mod <- rnModule (mi_module iface)
  exports <- mapM rnAvailInfo (mi_exports iface)
  decls <- mapM rnIfaceDecl' (mi_decls iface)
  deps <- rnDependencies (mi_deps iface)
  return $ iface & set_mi_module mod
                 & set_mi_exports exports
                 & set_mi_decls decls
                 & set_mi_deps deps

rnDependencies :: Rename Dependencies
rnDependencies deps0 = panic "rnDependencies"

{- *********************************************************************
*                                                                      *
                        ModIface substitution
*                                                                      *
********************************************************************* -}

initRnIface
  :: CsEnv
  -> ModIface
  -> [(ModuleName, Module)]
  -> Maybe NameShape
  -> ShIfM a
  -> IO (Either (Messages TcRnMessage) a)
initRnIface cs_env iface insts nsubst do_this = do
  errs_var <- newIORef emptyMessages
  let hsubst = listToUFM insts
      rn_mod = renameHoleModule (cs_units cs_env) hsubst
      env = ShIfEnv { sh_if_module = rn_mod (mi_module iface)
                    , sh_if_semantic_module = rn_mod (mi_semantic_module iface)
                    , sh_if_hole_subst = hsubst
                    , sh_if_shape = nsubst
                    , sh_if_errs = errs_var }
  res <- initTcRnIf 'c' cs_env env () $ tryM do_this
  msgs <- readIORef errs_var
  case res of
    Left _ -> return $ Left msgs
    Right r | not (isEmptyMessages msgs) -> return $ Left msgs
            | otherwise -> return $ Right r

data ShIfEnv = ShIfEnv
  { sh_if_module :: Module
  , sh_if_semantic_module :: Module
  , sh_if_hole_subst :: ShHoleSubst
  , sh_if_shape :: Maybe NameShape
  , sh_if_errs :: IORef (Messages TcRnMessage)
  }

type ShIfM = TcRnIf ShIfEnv ()
type Rename a = a -> ShIfM a

getHoleSubst :: ShIfM ShHoleSubst
getHoleSubst = fmap sh_if_hole_subst getGblEnv

rnModule :: Rename Module
rnModule mod = do
  hmap <- getHoleSubst
  unit_state <- cs_units <$> getTopEnv
  return $ renameHoleModule unit_state hmap mod

rnAvailInfo :: Rename AvailInfo
rnAvailInfo (Avail c) = Avail <$> rnIfaceGlobal c
rnAvailInfo (AvailTC n ns) = do
  ns' <- mapM rnIfaceGlobal ns
  case ns' of
    [] -> panic "rnAvailInfoEmpty AvailInfo"
    (rep:rest) -> assertPpr (all ((== childModule rep) . childModule) rest)
                            ( ppr rep $$ hcat (map ppr rest))
                  $ do n' <- setNameModule (Just (childModule rep)) n
                       return $ AvailTC n' ns'
  where
    childModule = nameModule
      
rnIfaceGlobal :: Rename Name
rnIfaceGlobal n = do
  cs_env <- getTopEnv
  let unit_state = cs_units cs_env
      home_unit = cs_home_unit cs_env
  iface_semantic_mod <- fmap sh_if_semantic_module getGblEnv
  mb_nsbust <- fmap sh_if_shape getGblEnv
  hmap <- getHoleSubst
  let m = nameModule n
      m' = renameHoleModule unit_state hmap m

  if | m' == iface_semantic_mod
     , isHoleModule m'
       -> do n' <- setNameModule (Just m') n
             case mb_nsubst of
               Nothing -> return n'
               Just nsubst -> panic "rnIfaceGlobal"
     | not (isHoleModule m)
       -> setNameModule (Just m') n
     | otherwise
       -> panic "rnIfaceGlobal holemodule"
               
rnIfaceDecl' :: Rename (Fingerprint, IfaceDecl)
rnIfaceDecl' (fp, decl) = (fp,) <$> rnIfaceDecl decl

rnIfaceDecl :: Rename IfaceDecl
-- rnIfaceDecl d@IfaceId{} = do
--   name <- rnIfaceGlobal (ifName d)
--   ty <- rnIfaceType (ifType d)
--   details <- rnIfaceIdDetails (ifIdDetails d)
--   info <- rnIfaceIdInfo (ifIdInfo d)
--   return d { ifName = name
--            , ifType = ty
--            , ifIdDetails = details
--            , ifIdInfo = info }

-- rnIfaceDecl d@IfaceData{} = do
--   name <- rnIfaceGlobal (ifName d)
--   binders

rnIfaceDecl _ = panic "rnIfaceDecl"
