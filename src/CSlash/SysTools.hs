module CSlash.SysTools where

import CSlash.Utils.Panic
import CSlash.Driver.Session

-- import GHC.SysTools.Tasks
import CSlash.SysTools.BaseDir
import CSlash.Settings.IO

import Control.Monad.Trans.Except (runExceptT)
import System.IO
import Foreign.Marshal.Alloc (allocaBytes)
import System.Directory (copyFile)

initSysTools :: String -> IO Settings
initSysTools top_dir = do
  res <- runExceptT $ initSettings top_dir
  case res of
    Right a -> pure a
    Left (SettingsError_MissingData msg) -> pgmError msg
    Left (SettingsError_BadData msg) -> pgmError msg
