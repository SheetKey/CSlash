module CSlash.SysTools.BaseDir
  ( expandTopDir, expandToolDir
  , findTopDir, findToolDir
  , tryFindTopDir
  ) where

import CSlash.BaseDir

import CSlash.Utils.Panic

import System.Environment (lookupEnv)
import System.FilePath

import GHC.SysTools.BaseDir (expandTopDir, expandToolDir, findToolDir)

findTopDir :: Maybe String -> IO String
findTopDir m_minusb = do
  maybe_exec_dir <- tryFindTopDir m_minusb
  case maybe_exec_dir of
    Nothing -> throwCsExceptionIO $
      InstallationError "missing -B<dir> option"
    Just dir -> return dir

tryFindTopDir :: Maybe String -> IO (Maybe String)
tryFindTopDir (Just minusb) = return $ Just $ normalise minusb
tryFindTopDir Nothing = getBaseDir
