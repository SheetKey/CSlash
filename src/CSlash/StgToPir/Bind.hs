module CSlash.StgToPir.Bind where

import Prelude hiding ((<>))

import CSlash.Core ( AltCon(..) )
import CSlash.Core.Opt.Arity ( isOneShotBndr )
-- import GHC.Runtime.Heap.Layout
import CSlash.Unit.Module

import CSlash.Stg.Syntax

import CSlash.Platform
import CSlash.Platform.Profile

-- import GHC.Builtin.Names (unpackCStringName, unpackCStringUtf8Name)

import CSlash.StgToPir.Config
-- import CSlash.StgToPir.Expr
import CSlash.StgToPir.Monad
import CSlash.StgToPir.Env
-- import GHC.StgToCmm.DataCon
-- import GHC.StgToCmm.Heap
-- import GHC.StgToCmm.Prof (ldvEnterClosure, enterCostCentreFun, enterCostCentreThunk,
--                    initUpdFrameProf)
-- import GHC.StgToCmm.TagCheck
-- import GHC.StgToCmm.Ticky
-- import GHC.StgToCmm.Layout
-- import GHC.StgToCmm.Utils
import CSlash.StgToPir.Function
-- import GHC.StgToCmm.Foreign    (emitPrimCall)

import CSlash.Pir.Graph
import CSlash.Pir.BlockId
import CSlash.Pir
-- import CSlash.Pir.Info
-- import CSlash.Pir.Utils
import CSlash.Pir.PLabel

import CSlash.Stg.Utils
-- import GHC.Types.CostCentre
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.Var.Class
import CSlash.Types.Name hiding (varName)
import CSlash.Types.Var.Set
import CSlash.Types.Basic
import CSlash.Types.Tickish ( tickishIsCode )

import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import CSlash.Data.FastString
import CSlash.Data.List.SetOps

import Control.Monad

------------------------------------------------------------------------
--              Top-level bindings
------------------------------------------------------------------------

cgTopRhsFunction
  :: Platform
  -> RecFlag
  -> CgId
  -> [CgId]
  -> CgStgExpr
  -> (CgIdInfo, FCode ())
cgTopRhsFunction platform is_rec id args body =
  let function_label = mkFunctionLabel (varName id) (idCafInfo id)
      lf_info = mkFunctionLFInfo platform id TopLevel False args
      cg_id_info = litIdInfo platform id lf_info (PirLabel function_label)
  in (cg_id_info, gen_code lf_info function_label)
  where
    gen_code :: LambdaFormInfo -> PLabel -> FCode ()
    gen_code _ function_label
      | StgApp f [] <- body
      , null args
      , isNonRec is_rec
      = do panic "gen_code ind_static?"

      | null args
      , Just gen <- isUnpackCStringFunction body
      = do panic "gen_code unpackCString"

    gen_code lf_info _ = do
      profile <- getProfile
      let name = varName id
      mod_name <- getModuleName
      let descr = functionDescription mod_name name
          function_info = mkFunctionInfo profile id lf_info descr

      forkFunctionBody (functionCodeBody True id function_info args body)

      return ()

-- TODO 
isUnpackCStringFunction :: CgStgExpr -> Maybe ()
isUnpackCStringFunction _ = Nothing

------------------------------------------------------------------------
--              Non-top-level bindings
------------------------------------------------------------------------
      
------------------------------------------------------------------------
--              Non-constructor right hand sides
------------------------------------------------------------------------

mkFunctionLFInfo
  :: Platform
  -> CgId
  -> TopLevelFlag
  -> Bool -- is join?
  -> [CgId]
  -> LambdaFormInfo
mkFunctionLFInfo platform bndr top is_join args
  = panic "mkFunctionLFInfo" -- mkLFReEntrant top args (mkArgDescr platform args)

------------------------------------------------------------------------
--              The code for functions
------------------------------------------------------------------------

functionCodeBody
  :: Bool
  -> CgId
  -> FunctionInfo
  -> [CgId]
  -> CgStgExpr
  -> FCode ()
functionCodeBody = panic "functionCodeBody"

------------------------------------------------------------------------
--              Profiling
------------------------------------------------------------------------

functionDescription :: Module -> Name -> String  
functionDescription mod_name name
  = showSDocOneLine defaultSDocContext
    (char '<' <> pprFullName mod_name name <> char '>')
