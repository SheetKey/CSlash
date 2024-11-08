module CSlash.Rename.Utils where

import CSlash.Core.Type
import CSlash.Cs
import CSlash.Types.Name.Reader
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad
import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.Name.Env
import CSlash.Core.DataCon
import CSlash.Types.SrcLoc as SrcLoc
import CSlash.Types.SourceFile
import CSlash.Types.SourceText ( SourceText(..), IntegralLit )
import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Unit.Module.ModIface
import CSlash.Utils.Panic
import CSlash.Types.Basic
import CSlash.Data.List.SetOps ( removeDupsOn )
import CSlash.Data.Maybe ( whenIsJust )
import CSlash.Driver.DynFlags
import CSlash.Data.FastString
import CSlash.Data.Bag ( mapBagM, headMaybe )
import Control.Monad
import CSlash.Settings.Constants ( mAX_TUPLE_SIZE{-, mAX_CTUPLE_SIZE-} )
import CSlash.Unit.Module
import CSlash.Unit.Module.Warnings  ( WarningTxt(..) )
import CSlash.Iface.Load

import qualified Data.List as List
import qualified Data.List.NonEmpty as NE
import Data.Foldable
import Data.Maybe

{- *****************************************************
*                                                      *
            Binding
*                                                      *
***************************************************** -}

newLocalBndrRn :: LocatedN RdrName -> RnM Name
newLocalBndrRn (L loc rdr_name)
  | Just name <- isExact_maybe rdr_name
  = return name
  | otherwise
  = do unless (isUnqual rdr_name) $ addErrAt (locA loc) (badQualBndrErr rdr_name)
       uniq <- newUnique
       return $ mkInternalName uniq (rdrNameOcc rdr_name) (locA loc)

bindLocalNames :: [Name] -> RnM a -> RnM a
bindLocalNames names = updLclCtxt $ \lcl_env ->
  let rdr_env' = extendLocalRdrEnvList (tcl_rdr lcl_env) names
  in lcl_env { tcl_rdr = rdr_env' }

{- *********************************************************************
*                                                                      *
            Envt utility functions
*                                                                      *
********************************************************************* -}

warnUnusedLocalBinds :: [Name] -> FreeVars -> RnM ()
warnUnusedLocalBinds = check_unused UnusedNameLocalBind

warnUnusedMatches :: [Name] -> FreeVars -> RnM ()
warnUnusedMatches = check_unused UnusedNameMatch

check_unused :: UnusedNameProv -> [Name] -> FreeVars -> RnM ()
check_unused prov bound_names used_names
  = warnUnused prov (filterOut (`elemNameSet` used_names) bound_names)

warnUnused :: UnusedNameProv -> [Name] -> RnM ()
warnUnused prov names = mapM_ (\nm -> warnUnused1 prov nm (nameOccName nm)) names

warnUnused1 :: UnusedNameProv -> Name -> OccName -> RnM ()
warnUnused1 prov child child_occ
  = when (reportable child child_occ) $
    warn_unused_name prov (nameSrcSpan child) child_occ

warn_unused_name :: UnusedNameProv -> SrcSpan -> OccName -> RnM ()
warn_unused_name prov span child_occ = addDiagnosticAt span (TcRnUnusedName child_occ prov)

reportable :: Name -> OccName -> Bool
reportable child child_occ
  | isWiredInName child
  = False
  | otherwise
  = not (startsWithUnderscore child_occ)



badQualBndrErr :: RdrName -> TcRnMessage
badQualBndrErr rdr_name = TcRnQualifiedBinder rdr_name

