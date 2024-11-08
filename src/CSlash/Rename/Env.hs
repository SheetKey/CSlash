module CSlash.Rename.Env where

import CSlash.Iface.Load
import CSlash.Iface.Env
import CSlash.Cs
import CSlash.Types.Name.Reader
import CSlash.Tc.Errors.Types
-- import CSlash.Tc.Errors.Ppr (pprScopeError)
-- import CSlash.Tc.Utils.Env
import CSlash.Tc.Types.LclEnv
import CSlash.Tc.Utils.Monad
-- import CSlash.Parser.PostProcess ( setRdrNameSpace )
import CSlash.Builtin.Types
import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.Name.Env
import CSlash.Types.Avail
import CSlash.Types.Hint
import CSlash.Types.Error
import CSlash.Unit.Module
import CSlash.Unit.Module.ModIface
import CSlash.Core.ConLike
import CSlash.Core.DataCon
import CSlash.Core.TyCon
import CSlash.Builtin.Names( rOOT_MAIN )
import CSlash.Types.Basic  ( TopLevelFlag(..), TupleSort(..), tupleSortBoxity )
-- import CSlash.Types.TyThing ( tyThingGREInfo )
import CSlash.Types.SrcLoc as SrcLoc
import CSlash.Utils.Outputable as Outputable
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.Set
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Data.Maybe
import CSlash.Driver.Env
import CSlash.Driver.Session
import CSlash.Data.FastString
import CSlash.Data.List.SetOps ( minusList )
-- import qualified GHC.LanguageExtensions as LangExt
-- import CSlash.Rename.Unbound
import CSlash.Rename.Utils
import CSlash.Data.Bag
import CSlash.Types.PkgQual
import CSlash.Types.GREInfo

import Control.Arrow    ( first )
import Control.Monad
import Data.Either      ( partitionEithers )
import Data.Function    ( on )
import Data.List        ( find, partition, groupBy, sortBy )
import qualified Data.List.NonEmpty as NE
import qualified Data.Semigroup as Semi
import System.IO.Unsafe ( unsafePerformIO )

{- *****************************************************
*                                                      *
                Source-code binders
*                                                      *
***************************************************** -}

newTopSrcBinder :: LocatedN RdrName -> RnM Name
newTopSrcBinder (L loc rdr_name)
  | Just name <- isExact_maybe rdr_name
  = if isExternalName name
    then do this_mod <- getModule
            unless (this_mod == nameModule name) $
              addErrAt (locA loc) (TcRnBindingOfExistingName rdr_name)
            return name
    else do this_mod <- getModule
            externalizeName this_mod name
  | Just (rdr_mod, rdr_occ) <- isOrig_maybe rdr_name
  = do this_mod <- getModule
       unless (rdr_mod == this_mod || rdr_mod == rOOT_MAIN) $
         addErrAt (locA loc) (TcRnBindingOfExistingName rdr_name)
       newGlobalBinder rdr_mod rdr_occ (locA loc)
  | otherwise
  = do when (isQual rdr_name) $
         addErrAt (locA loc) (badQualBndrErr rdr_name)
       this_mod <- getModule
       traceRn "newTopSrcBinder" (ppr this_mod $$ ppr rdr_name $$ ppr (locA loc))
       newGlobalBinder this_mod (rdrNameOcc rdr_name) (locA loc)

data CsSigCtxt
  = TopSigCtxt NameSet
  | LocalBindCtxt NameSet

instance Outputable CsSigCtxt where
  ppr (TopSigCtxt ns) = text "TopSigCtxt" <+> ppr ns
  ppr (LocalBindCtxt ns) = text "LocalBindCtxt" <+> ppr ns
