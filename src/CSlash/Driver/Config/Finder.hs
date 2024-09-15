module CSlash.Driver.Config.Finder
  ( FinderOpts(..)
  , initFinderOpts
  ) where

import CSlash.Driver.DynFlags
import CSlash.Unit.Finder.Types
import CSlash.Data.FastString

initFinderOpts :: DynFlags -> FinderOpts
initFinderOpts flags = FinderOpts
  { finder_importPaths = importPaths flags
  , finder_lookupHomeInterfaces = isOneShot (csMode flags)
  , finder_bypassHiFileCheck = MkDepend == (csMode flags)
  , finder_ways = ways flags
  , finder_enableSuggestions = gopt Opt_HelpfulErrors flags
  , finder_workingDirectory = workingDirectory flags
  , finder_thisPackageName = mkFastString <$> thisPackageName flags
  , finder_hiddenModules = hiddenModules flags
  , finder_reexportedModules = reexportedModules flags
  , finder_hieDir = hieDir flags
  , finder_hieSuf = hieSuf flags
  , finder_hiDir = hiDir flags
  , finder_hiSuf = hiSuf_ flags
  , finder_dynHiSuf = dynHiSuf_ flags
  , finder_objectDir = objectDir flags
  , finder_objectSuf = objectSuf_ flags
  , finder_dynObjectSuf = dynObjectSuf_ flags
  , finder_stubDir = stubDir flags
  }
