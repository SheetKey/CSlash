{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Type.Tidy where

import CSlash.Data.FastString

import CSlash.Core.Type.Rep
import CSlash.Core.Kind
import CSlash.Core.Type.FVs (tyKiVarsOfTypeList)
import CSlash.Core.Kind.FVs (kiVarsOfKindList)

import CSlash.Types.Name hiding (varName)
import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Utils.Misc (strictMap)

import Data.List (mapAccumL)

{- *********************************************************************
*                                                                      *
            TidyType
*                                                                      *
********************************************************************* -}

tidyVarBndr :: TidyEnv -> Var -> (TidyEnv, Var)
tidyVarBndr tidy_env@(occ_env, subst) var
  = case tidyOccName occ_env (getHelpfulOccName var) of
      (occ_env', occ') -> ((occ_env', subst'), var')
        where
          subst' = extendVarEnv subst var var'
          var' = updateVarKindSafe (tidyKind tidy_env) (setVarName var name')
          name' = tidyNameOcc name occ'
          name = varName var

avoidNameClashes :: [TypeVar] -> TidyEnv -> TidyEnv
avoidNameClashes tvs (occ_env, subst)
  = (avoidClashesOccEnv occ_env occs, subst)
  where occs = map getHelpfulOccName tvs

getHelpfulOccName :: Var -> OccName
getHelpfulOccName v
  | isSystemName name, isTcTyVar v
  = mkTyVarOccFS (occNameFS occ `appendFS` fsLit "0")
  | isSystemName name, isTcKiVar v
  = mkKiVarOccFS (occNameFS occ `appendFS` fsLit "0")
  | otherwise
  = occ
  where
    name = varName v
    occ = getOccName name

tidyForAllTyBinder :: TidyEnv -> VarBndr TypeVar vis -> (TidyEnv, VarBndr TypeVar vis)
tidyForAllTyBinder tidy_env (Bndr tv vis) = (tidy_env', Bndr tv' vis)
  where (tidy_env', tv') = tidyVarBndr tidy_env tv

tidyForAllTyBinders :: TidyEnv -> [VarBndr TypeVar vis] -> (TidyEnv, [VarBndr TypeVar vis])
tidyForAllTyBinders tidy_env tvbs
  = mapAccumL tidyForAllTyBinder (avoidNameClashes (binderVars tvbs) tidy_env) tvbs

tidyTyLamTyBinder :: TidyEnv -> TypeVar -> (TidyEnv, TypeVar)
tidyTyLamTyBinder tidy_env tv = (tidy_env', tv')
  where (tidy_env', tv') = tidyVarBndr tidy_env tv

tidyTyLamTyBinders :: TidyEnv -> [TypeVar] -> (TidyEnv, [TypeVar])
tidyTyLamTyBinders tidy_env tvbs
  = mapAccumL tidyTyLamTyBinder (avoidNameClashes tvbs tidy_env) tvbs

tidyFreeTyKiVars :: TidyEnv -> [Var] -> TidyEnv
tidyFreeTyKiVars tidy_env vars = fst (tidyOpenTyKiVars tidy_env vars)

tidyOpenTyKiVars :: TidyEnv -> [Var] -> (TidyEnv, [Var])
tidyOpenTyKiVars env vars = mapAccumL tidyOpenTyKiVar env vars

tidyOpenTyKiVar :: TidyEnv -> Var -> (TidyEnv, Var)
tidyOpenTyKiVar env@(_, subst) var = case lookupVarEnv subst var of
  Just var' -> (env, var')
  Nothing -> let env' = if isTyVar var
                        then tidyFreeTyKiVars env (kiVarsOfKindList (tyVarKind var))
                        else env
             in tidyVarBndr env' var

tidyTyKiVarOcc :: TidyEnv -> Var -> Var
tidyTyKiVarOcc env@(_, subst) v = case lookupVarEnv subst v of
                                    Nothing -> updateVarKindSafe (tidyKind env) v
                                    Just v' -> v'

tidyKind :: TidyEnv -> Kind -> Kind
tidyKind env (KiVarKi kv) = KiVarKi $! tidyTyKiVarOcc env kv
tidyKind _ kc@(KiCon _) = kc
tidyKind env ki@(FunKd _ arg res) = let !arg' = tidyKind env arg
                                        !res' = tidyKind env res
                                    in ki { kft_arg = arg', kft_res = res' }
tidyKind env (KdContext rels) = KdContext $! tidyKindRels env rels

tidyKindRels :: TidyEnv -> [KdRel] -> [KdRel]
tidyKindRels env = map (tidyKindRel env)

tidyKindRel :: TidyEnv -> KdRel -> KdRel
tidyKindRel env (LTKd k1 k2) = let !k1' = tidyKind env k1
                                   !k2' = tidyKind env k2
                               in LTKd k1' k2'
tidyKindRel env (LTEQKd k1 k2) = let !k1' = tidyKind env k1
                                     !k2' = tidyKind env k2
                                 in LTKd k1' k2'
