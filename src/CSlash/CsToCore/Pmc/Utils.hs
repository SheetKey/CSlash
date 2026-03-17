module CSlash.CsToCore.Pmc.Utils where

import CSlash.Types.Basic (Origin(..), requiresPMC)
import CSlash.Driver.DynFlags
import CSlash.Cs
import CSlash.Core.Type
import CSlash.Data.FastString
import CSlash.Data.IOEnv
import CSlash.Data.Maybe
import CSlash.Types.Var.Id
import CSlash.Types.Name
import CSlash.Types.Unique.Supply
import CSlash.Types.SrcLoc
import CSlash.Utils.Outputable
import CSlash.Utils.Logger
import CSlash.CsToCore.Monad

import Control.Monad

tracePm :: String -> SDoc -> DsM ()
tracePm herald doc = do
  logger <- getLogger
  name_ppr_ctx <- mkNamePprCtxDs
  liftIO $ putDumpFileMaybe' logger name_ppr_ctx
           Opt_D_dump_ec_trace "" FormatText (text herald $$ (nest 2 doc))
{-# INLINE tracePm #-}

traceWhenFailPm :: String -> SDoc -> MaybeT DsM a -> MaybeT DsM a
traceWhenFailPm herald doc act = MaybeT $ do
  mb_a <- runMaybeT act
  when (isNothing mb_a) $ tracePm herald doc
  pure mb_a
{-# INLINE traceWhenFailPm #-}

mkPmId :: Type Zk -> DsM (Id Zk)
mkPmId ty = getUniqueM >>= \unique ->
  let occname = mkVarOccFS $ fsLit "pm"
  in return (mkUserLocal occname unique ty noSrcSpan)
{-# NOINLINE mkPmId #-}

allPmCheckWarnings :: [WarningFlag]
allPmCheckWarnings =
  [ Opt_WarnIncompletePatterns
  , Opt_WarnIncompleteUniPatterns
  , Opt_WarnOverlappingPatterns
  ]

isMatchContextPmChecked :: DynFlags -> Origin -> CsMatchContext p -> Bool
isMatchContextPmChecked dflags origin ctxt
  = requiresPMC origin
    && (overlapping dflags ctxt || exhaustive dflags ctxt)

isMatchContextPmChecked_SinglePat :: DynFlags -> Origin -> CsMatchContext p -> LPat Zk -> Bool
isMatchContextPmChecked_SinglePat dflags origin ctxt pat
  | not (needToRunPmCheck dflags origin)
  = False
  | StmtCtxt {} <- ctxt
  = not (isBoringCsPat pat)
  | otherwise
  = overlapping dflags ctxt || exhaustive dflags ctxt

needToRunPmCheck :: DynFlags -> Origin -> Bool
needToRunPmCheck dflags origin
  = requiresPMC origin
    && any (`wopt` dflags) allPmCheckWarnings

overlapping :: DynFlags -> CsMatchContext p -> Bool
overlapping dflags _ = wopt Opt_WarnOverlappingPatterns dflags

exhaustive :: DynFlags -> CsMatchContext p -> Bool
exhaustive dflags = maybe False (`wopt` dflags) . exhaustiveWarningFlag

exhaustiveWarningFlag :: CsMatchContext p -> Maybe WarningFlag
exhaustiveWarningFlag LamAlt = Just Opt_WarnIncompleteUniPatterns
exhaustiveWarningFlag TyLamAlt = Just Opt_WarnIncompleteUniPatterns
exhaustiveWarningFlag CaseAlt = Just Opt_WarnIncompletePatterns
exhaustiveWarningFlag MultiIfAlt = Just Opt_WarnIncompletePatterns
exhaustiveWarningFlag TyLamTyAlt = Just Opt_WarnIncompleteUniPatterns
exhaustiveWarningFlag StmtCtxt{} = Nothing
