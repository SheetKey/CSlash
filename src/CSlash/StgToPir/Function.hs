{-# LANGUAGE MultiParamTypeClasses #-}

module CSlash.StgToPir.Function
  ( module CSlash.StgToPir.Function
  , LambdaFormInfo
  ) where

import CSlash.Cs.Pass
import CSlash.Platform
import CSlash.Platform.Profile

import CSlash.Stg.Syntax
-- import GHC.Runtime.Heap.Layout
import CSlash.Pir
-- import CSlash.Pir.Utils
import CSlash.StgToPir.Types
import CSlash.StgToPir.Sequel

-- import GHC.Types.CostCentre
import CSlash.Pir.BlockId
import CSlash.Pir.PLabel
import CSlash.Types.Var.Id
import CSlash.Types.Var.Class
import CSlash.Types.Var.Id.Info
import CSlash.Core.DataCon
import CSlash.Types.Name hiding (varName)
import CSlash.Core.Type
import CSlash.Tc.Utils.TcType
import CSlash.Core.TyCon
import CSlash.Types.RepType
import CSlash.Types.Basic
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Data.Maybe (isNothing)

import Data.Coerce (coerce)
import qualified Data.ByteString.Char8 as BS8
import CSlash.StgToPir.Config
-- import GHC.Stg.InferTags.TagSig (isTaggedSig)

-----------------------------------------------------------------------------
--                Data types and synonyms
-----------------------------------------------------------------------------

data CgLoc
  = PirLoc PirExpr
  | LneLoc BlockId [LocalReg]

instance OutputableP Platform CgLoc where
  pdoc = pprCgLoc

pprCgLoc :: Platform -> CgLoc -> SDoc
pprCgLoc platform (PirLoc e) = text "pir" <+> pdoc platform e
pprCgLoc _ (LneLoc b rs) = text "lne" <+> ppr b <+> ppr rs

-------------------------------------
--        Non-void types
-------------------------------------

newtype NonVoid a = NonVoid a
  deriving (Eq, Show)

fromNonVoid :: NonVoid a -> a
fromNonVoid (NonVoid a) = a

instance (Outputable a) => Outputable (NonVoid a) where
  ppr (NonVoid a) = ppr a

nonVoidIds :: [Id Zk] -> [NonVoid (Id Zk)]
nonVoidIds ids = [NonVoid id | id <- ids, not (isZeroBitTy (varType id))]

nonVoidStgArgs :: [StgArg] -> [NonVoid StgArg]
nonVoidStgArgs args = [NonVoid arg | arg <- args, not (null (stgArgRep arg))]

------------------------------------------------------
--                Building LambdaFormInfo
------------------------------------------------------

mkLFArgument :: Id Zk -> LambdaFormInfo
mkLFArgument id
  | mightBeFunTy (varType id) = LFUnknown True
  | otherwise = LFUnknown False

mkLFReEntrant
  :: TopLevelFlag
  -> [Id Zk]
  -> LambdaFormInfo
mkLFReEntrant _ [] = pprPanic "mkLFReEntrant" empty
mkLFReEntrant top args = LFReEntrant top (length args) False

mkLFConst :: Type Zk -> TopLevelFlag -> Bool -> LambdaFormInfo
mkLFConst ty top is_join
  = assertPpr (not (mightBeFunTy ty))
    (vcat [ text "mkLFConst migh be fun ty"
          , text "ty" <+> ppr ty ]) $
    LFConst top is_join

importedIdLFInfo :: Id Zk -> LambdaFormInfo
importedIdLFInfo id = case idLFInfo_maybe id of
  Just lf_info -> lf_info
  Nothing -> let arity = idFunRepArity id
    in if arity > 0
       then LFReEntrant TopLevel arity True
       else assert (isNothing (isDataConId_maybe id)) $
            mkLFArgument id

-----------------------------------------------------------------------------
--              Data types for function information
-----------------------------------------------------------------------------

data FunctionInfo = FunctionInfo
  { functionName :: !(Id Zk)
  , functionLFInfo :: !LambdaFormInfo
  , functionLabel :: !PLabel
  , functionProf :: !ProfilingInfo
  }

--------------------------------------
--        Building FunctionInfos
--------------------------------------

mkFunctionInfo
  :: Profile
  -> Id Zk
  -> LambdaFormInfo
  -> String
  -> FunctionInfo
mkFunctionInfo profile id lf_info val_descr
  = FunctionInfo { functionName = id
                 , functionLFInfo = lf_info
                 , functionLabel = lbl
                 , functionProf = prof }
  where
    prof = mkProfilingInfo profile id val_descr
    lbl = mkFunctionLabel (varName id) (idCafInfo id)

-----------------------------------------------------------------------------
--                getCallMethod
-----------------------------------------------------------------------------

data CallMethod
  = ReturnIt
  | DirectEntry PLabel RepArity

instance Outputable CallMethod where
  ppr ReturnIt = text "ReturnIt"
  ppr DirectEntry{} = text "DirectEntry"

getCallMethod
  :: StgToPirConfig
  -> Name
  -> Id Zk
  -> LambdaFormInfo
  -> RepArity
  -> CgLoc
  -> Maybe SelfLoopInfo
  -> CallMethod
getCallMethod cfg _ id _ n_args _ (Just self_loop) = panic "getCallMethod 1"

getCallMethod cfg name id (LFReEntrant _ arity _) n_args _ _ 
  | n_args == 0
    && not (profileIsProfiling (stgToPirProfile cfg))
  = assert (arity /= 0) ReturnIt
  | n_args < arity = panic "getCallMethod SlowCall"
  | otherwise = DirectEntry (enterIdLabel (stgToPirPlatform cfg) name (idCafInfo id)) arity

getCallMethod _ _ _ (LFCon _) n_args _ _ = panic "getCallMethod 3"

getCallMethod cfg name id (LFConst _ is_join) n_args _ _ = panic "getCallMethod 4"

getCallMethod cfg name id (LFUnknown might_be_a_function) n_args _ _ = panic "getCallMethod 5"

--------------------------------------
--   Label generation
--------------------------------------

enterIdLabel :: Platform -> Name -> CafInfo -> PLabel
enterIdLabel platform id c
  -- | platformTablesNextToCode platform = panic "mkInfoTableLabel id c"
  | otherwise = mkEntryLabel id c

--------------------------------------
--   Profiling
--------------------------------------

mkProfilingInfo :: Profile -> Id Zk -> String -> ProfilingInfo
mkProfilingInfo profile id val_descr
  | not (profileIsProfiling profile) = NoProfilingInfo
  | otherwise = panic "profiling"
