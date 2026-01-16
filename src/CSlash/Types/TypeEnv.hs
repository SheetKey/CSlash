module CSlash.Types.TypeEnv where

-- import GHC.Core.Class
-- import GHC.Core.Coercion.Axiom
import CSlash.Core.ConLike
import CSlash.Core.DataCon
-- import GHC.Core.FamInstEnv
-- import GHC.Core.PatSyn
import CSlash.Core.TyCon

import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Var
import CSlash.Types.TyThing

type TypeEnv = NameEnv (TyThing (TyVar KiVar) KiVar)

emptyTypeEnv :: TypeEnv
emptyTypeEnv = emptyNameEnv

plusTypeEnv :: TypeEnv -> TypeEnv -> TypeEnv
plusTypeEnv env1 env2 = plusNameEnv env1 env2

lookupTypeEnv :: TypeEnv -> Name -> Maybe (TyThing (TyVar KiVar) KiVar)
lookupTypeEnv = lookupNameEnv

extendTypeEnv :: TypeEnv -> TyThing (TyVar KiVar) KiVar -> TypeEnv
extendTypeEnv env thing = extendNameEnv env (getName thing) thing

extendTypeEnvList :: TypeEnv -> [TyThing (TyVar KiVar) KiVar] -> TypeEnv
extendTypeEnvList env things = foldl' extendTypeEnv env things

typeEnvElts :: TypeEnv -> [TyThing (TyVar KiVar) KiVar]
typeEnvElts env = nonDetNameEnvElts env

typeEnvIds :: TypeEnv -> [Id (TyVar KiVar) KiVar]
typeEnvIds env = [id | AnId id <- typeEnvElts env]

typeEnvTyCons :: TypeEnv -> [TyCon (TyVar KiVar) KiVar]
typeEnvTyCons env = [tc | ATyCon tc <- typeEnvElts env]

typeEnvDataCons :: TypeEnv -> [DataCon (TyVar KiVar) KiVar]
typeEnvDataCons env = [dc | AConLike (RealDataCon dc) <- typeEnvElts env]
