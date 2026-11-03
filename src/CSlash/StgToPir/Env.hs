module CSlash.StgToPir.Env
  ( module CSlash.StgToPir.Env
  , CgIdInfo
  ) where

import CSlash.Platform
import CSlash.StgToPir.Monad
import CSlash.StgToPir.Function
import CSlash.Stg.Syntax

import CSlash.Pir.PLabel

import CSlash.Pir.BlockId
import CSlash.Pir.Expr
-- import CSlash.Pir.Utils
import CSlash.Pir.Graph
import CSlash.Types.Var.Id
import CSlash.Types.Var.Class
import CSlash.Types.Name hiding (varName)
import CSlash.Types.RepType
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

idInfoToAmode :: CgIdInfo -> PirExpr
idInfoToAmode CgIdInfo { cg_loc = PirLoc e } = e
idInfoToAmode cg_info = pprPanic "idInfoToAmode" (ppr (cg_id cg_info))

-------------------------------------------------------------------------
--        Amodes for arguments
-------------------------------------------------------------------------

getArgAmode :: NonVoid StgArg -> FCode PirExpr
getArgAmode (NonVoid (StgVarArg var)) = idInfoToAmode <$> getCgIdInfo var
getArgAmode (NonVoid (StgLitArg lit)) = panic "cgLit lit"

getNonVoidArgAmodes :: [StgArg] -> FCode [PirExpr]
getNonVoidArgAmodes args = mapM getArgAmode (nonVoidStgArgs args)

---------------------------------------------------------
--        The binding environment
---------------------------------------------------------

addBindC :: CgIdInfo -> FCode ()
addBindC stuff_to_bind = do
  binds <- getBinds
  setBinds $ extendVarEnv binds (cg_id stuff_to_bind) stuff_to_bind

getCgIdInfo :: CgId -> FCode CgIdInfo
getCgIdInfo id = do
  platform <- getPlatform
  local_binds <- getBinds
  case lookupVarEnv local_binds id of
    Just info -> return info
    Nothing -> do
      let name = varName id
      if isExternalName name then
        let ext_lbl
              | [FunAddrRep] <- typePrimRep (varType id)
              = mkFunctionLabel name $ idCafInfo id
              | otherwise
              = pprPanic "getCgIdInfo unfinished" (ppr id)
        in return $ litIdInfo platform id (importedIdLFInfo id) (PirLabel ext_lbl)

        else pprPanic "getCgIdInfo non-local non-external" (ppr id)

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
