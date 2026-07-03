module CSlash.StgToPir.Env
  ( module CSlash.StgToPir.Env
  , CgIdInfo
  ) where

import CSlash.Platform
import CSlash.StgToPir.Monad
import CSlash.StgToPir.Function

import CSlash.Pir.PLabel

import CSlash.Pir.BlockId
import CSlash.Pir.Expr
-- import CSlash.Pir.Utils
import CSlash.Pir.Graph
import CSlash.Types.Var.Id
import CSlash.Types.Var.Class
import CSlash.Types.Name
import CSlash.Core.Type
import CSlash.Core.Type.Compare( eqType )
import CSlash.Builtin.Types.Prim
import CSlash.Types.Unique.FM
import CSlash.Types.Var.Env

import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import CSlash.Builtin.Names (getUnique)

-------------------------------------
--        Manipulating CgIdInfo
-------------------------------------

mkCgIdInfo :: CgId -> LambdaFormInfo -> PirExpr -> CgIdInfo
mkCgIdInfo id lf expr
  = CgIdInfo { cg_id = id
             , cg_lf = lf
             , cg_loc = PirLoc expr }

litIdInfo :: Platform -> CgId -> LambdaFormInfo -> PirLit -> CgIdInfo
litIdInfo platform id lf lit
  = CgIdInfo { cg_id = id
             , cg_lf = lf
             , cg_loc = PirLoc (PirLit lit) }

---------------------------------------------------------
--        The binding environment
---------------------------------------------------------

addBindC :: CgIdInfo -> FCode ()
addBindC stuff_to_bind = do
  binds <- getBinds
  setBinds $ extendVarEnv binds (cg_id stuff_to_bind) stuff_to_bind

------------------------------------------------------------------------
--        Interface functions for binding and re-binding names
------------------------------------------------------------------------

bindToReg :: NonVoid CgId -> LambdaFormInfo -> FCode LocalReg
bindToReg nvid@(NonVoid id) lf_info = do
  platform <- getPlatform
  let reg = idToReg platform nvid
  addBindC (mkCgIdInfo id lf_info (PirReg reg))
  return reg

bindArgToReg :: NonVoid CgId -> FCode LocalReg
bindArgToReg nvid@(NonVoid id) = bindToReg nvid (panic "mkLFArgument id")

bindArgsToRegs :: [NonVoid CgId] -> FCode [LocalReg]
bindArgsToRegs = mapM bindArgToReg

idToReg :: Platform -> NonVoid CgId -> LocalReg
idToReg platform (NonVoid id)
  = LocalReg (varUnique id) (panic "primRepPirType platform (idPrimRepU id)")
