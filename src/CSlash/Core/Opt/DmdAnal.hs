{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Opt.DmdAnal (dmdAnalProgram) where

{-
TODO(performance): Introduce weak demands:
In GHC, a weak demand is 'lazy used many times'
In CSL, a weak demand \could be\ 'strict used many times'
We would have to ensure that consumers of dmdsigs use this as the default in the absense of
an explicit sig in the environment.

As GHC says, this would improve performance of fixpointing the dmd.
-}

import CSlash.Cs.Pass

import CSlash.Types.Demand

import CSlash.Core as Core
import CSlash.Core.DataCon
import CSlash.Core.Utils
import CSlash.Core.TyCon
import CSlash.Core.Type
-- import GHC.Core.Predicate( isEqualityClass, isCTupleClass )
import CSlash.Core.FVs ( bndrRuleAndUnfoldingIds, rulesRhsFreeIds )
-- import GHC.Core.Coercion ( Coercion )
-- import GHC.Core.TyCo.FVs     ( coVarsOfCos )
import CSlash.Core.Type.Compare ( eqType )
import CSlash.Core.Opt.Arity ( typeArity )

import CSlash.Builtin.Names
-- import GHC.Builtin.PrimOps
-- import GHC.Builtin.Types.Prim ( realWorldStatePrimTy )

import CSlash.Types.Unique.Set
-- import CSlash.Types.Unique.MemoFun
import CSlash.Types.RepType
-- import CSlash.Types.ForeignCall ( isSafeForeignCall )
import CSlash.Types.Var.Id
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Var.Class
import CSlash.Types.Basic

import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Outputable

import Data.List        ( mapAccumL )

{- *********************************************************************
*                                                                      *
          Top level stuff
*                                                                      *
********************************************************************* -}

data WithDmdType a = WithDmdType !DmdType !a

getAnnotated :: WithDmdType a -> a
getAnnotated (WithDmdType _ a) = a

data DmdResult a b = R !a !b

dmdAnalProgram :: [CoreRule] -> CoreProgram -> CoreProgram
dmdAnalProgram rules binds
  = getAnnotated $ go emptyAnalEnv binds
  where
    go _ [] = WithDmdType nopDmdType []
    go env (b:bs) = cons_up $ dmdAnalBind TopLevel env topSubDmd b anal_body
      where
        anal_body env'
          = let WithDmdType body_ty bs' = go env' bs
            in WithDmdType (body_ty `plusDmdType` keep_alive_roots env' (bindersOf b)) bs'

    cons_up :: WithDmdType (DmdResult b [b]) -> WithDmdType [b]
    cons_up (WithDmdType dmd_ty (R b' bs')) = WithDmdType dmd_ty (b' : bs')

    keep_alive_roots :: AnalEnv -> [CoreId] -> DmdEnv
    keep_alive_roots env ids = plusDmdEnvs (map (demandRoot env) (filter is_root ids))

    is_root :: CoreId -> Bool
    is_root id = isExportedId id || elemVarSet id rule_fvs

    rule_fvs :: CoreIdSet
    rule_fvs = rulesRhsFreeIds rules

demandRoot :: AnalEnv -> CoreId -> DmdEnv
demandRoot env id = fst (dmdAnalStar env topDmd (Var id))

demandRoots :: AnalEnv -> [CoreId] -> DmdEnv
demandRoots env roots = plusDmdEnvs (map (demandRoot env) roots)

demandRootSet :: AnalEnv -> IdSet Zk -> DmdEnv
demandRootSet env ids = demandRoots env (nonDetEltsUniqSet ids)

isInterestingTopLevelFn :: CoreId -> Bool
isInterestingTopLevelFn id = typeArity (varType id) > 0

{- *********************************************************************
*                                                                      *
          The analyzer
*                                                                      *
********************************************************************* -}

dmdAnalBind
  :: TopLevelFlag
  -> AnalEnv
  -> SubDemand
  -> CoreBind
  -> (AnalEnv -> WithDmdType a)
  -> WithDmdType (DmdResult CoreBind a)
dmdAnalBind top_lvl env dmd bind anal_body = case bind of
  NonRec id rhs
    | useLetUp top_lvl id
    -> dmdAnalBindLetUp top_lvl env id rhs anal_body
  _ -> dmdAnalBindLetDown top_lvl env dmd bind anal_body

setBindIdDemandInfo :: TopLevelFlag -> CoreId -> Demand -> CoreId
setBindIdDemandInfo top_lvl id dmd = setIdDemandInfo id $ case top_lvl of
  TopLevel | not (isInterestingTopLevelFn id) -> topDmd
  _ -> dmd

dmdAnalBindLetUp
  :: TopLevelFlag
  -> AnalEnv
  -> CoreId
  -> CoreExpr
  -> (AnalEnv -> WithDmdType a)
  -> WithDmdType (DmdResult CoreBind a)
dmdAnalBindLetUp top_lvl env id rhs anal_body
  = WithDmdType final_ty (R (NonRec id' rhs') (body'))
  where
    WithDmdType body_ty body' = anal_body (addInScopeAnalEnv env id)

    WithDmdType body_ty' id_dmd' = findBndrDmd env body_ty id

    !id' = setBindIdDemandInfo top_lvl id id_dmd'
    (rhs_ty, rhs') = dmdAnalStar env id_dmd' rhs

    rule_fvs = bndrRuleAndUnfoldingIds id
    final_ty = body_ty' `plusDmdType` rhs_ty `plusDmdType` demandRootSet env rule_fvs

dmdAnalBindLetDown
  :: TopLevelFlag
  -> AnalEnv
  -> SubDemand
  -> CoreBind
  -> (AnalEnv -> WithDmdType a)
  -> WithDmdType (DmdResult CoreBind a)
dmdAnalBindLetDown top_lvl env dmd bind anal_body = case bind of
  NonRec id rhs
    -> let (env', id1, rhs1) = dmdAnalRhsSig top_lvl NonRecursive env dmd id rhs
       in do_rest env' [(id1, rhs1)] (uncurry NonRec . only)
  Rec pairs
    -> let (env', pairs') = dmdFix top_lvl env dmd pairs
       in do_rest env' pairs' Rec
  where
    do_rest env' pairs1 build_bind = WithDmdType final_ty (R (build_bind pairs2) body')
      where
        WithDmdType body_ty body' = anal_body env'
        WithDmdType final_ty id_dmds = findBndrsDmds env' body_ty (strictMap fst pairs1)
        !pairs2 = strictZipWith do_one pairs1 id_dmds
        do_one (id', rhs') dmd = ((,) $! setBindIdDemandInfo top_lvl id' dmd) $! rhs'

anticipateANF :: CoreExpr -> Card -> Card
anticipateANF e n
  | exprIsTrivial e = n
  | not (isAbs n && exprOkForSpeculation e) = C_11
  | otherwise = oneifyCard n

dmdAnalStar
  :: AnalEnv
  -> Demand
  -> CoreExpr
  -> (DmdEnv, CoreExpr)
dmdAnalStar env (n :* sd) e
  = let WithDmdType dmd_ty e' = dmdAnal env sd e
        n' = anticipateANF e n
    in (multDmdEnv n' (discardArgDmds dmd_ty), e')

dmdAnal :: AnalEnv -> SubDemand -> CoreExpr -> WithDmdType CoreExpr
dmdAnal env d e = dmdAnal' env d e

dmdAnal' :: AnalEnv -> SubDemand -> CoreExpr -> WithDmdType CoreExpr
dmdAnal' _ _ (Lit lit) = WithDmdType nopDmdType (Lit lit)
dmdAnal' _ _ (Type ty) = WithDmdType nopDmdType (Type ty)
dmdAnal' _ _ (KiCo co) = WithDmdType nopDmdType (KiCo co)
dmdAnal' _ _ (Kind ki) = WithDmdType nopDmdType (Kind ki)
dmdAnal' env dmd (Var var) = WithDmdType (dmdTransform env var dmd) (Var var)
dmdAnal' env dmd (Cast e co)
  = WithDmdType dmd_ty (Cast e' co)
  where WithDmdType dmd_ty e' = dmdAnal env dmd e
dmdAnal' env dmd (Tick t e)
  = WithDmdType dmd_ty (Tick t e')
  where WithDmdType dmd_ty e' = dmdAnal env dmd e

dmdAnal' env dmd (App fun (Type ty))
  = WithDmdType fun_ty (App fun' (Type ty))
  where WithDmdType fun_ty fun' = dmdAnal env dmd fun
dmdAnal' env dmd (App fun (KiCo co))
  = WithDmdType fun_ty (App fun' (KiCo co))
  where WithDmdType fun_ty fun' = dmdAnal env dmd fun
dmdAnal' env dmd (App fun (Kind ki))
  = WithDmdType fun_ty (App fun' (Kind ki))
  where WithDmdType fun_ty fun' = dmdAnal env dmd fun
dmdAnal' env dmd (App fun arg)
  = let call_dmd = mkCalledOnceDmd dmd
        WithDmdType fun_ty fun' = dmdAnal env call_dmd fun
        (arg_dmd, res_ty) = splitDmdTy fun_ty
        (arg_ty, arg') = dmdAnalStar env arg_dmd arg
    in WithDmdType (res_ty `plusDmdType` arg_ty) (App fun' arg')
dmdAnal' env dmd (Lam var ki body)
  | Core.Id id <- var
  = let (n, body_dmd) = peelCallDmd dmd
        WithDmdType body_ty body' = dmdAnal (addInScopeAnalEnv env id) body_dmd body
        WithDmdType lam_ty id' = annotateLamIdBndr env body_ty id
        new_dmd_type = multDmdType n lam_ty
    in WithDmdType new_dmd_type (Lam (Core.Id id') ki body')
  | otherwise
  = let WithDmdType body_ty body' = dmdAnal env dmd body -- don't need to add var to scope since we never look inside types/kicos/kinds
    in WithDmdType body_ty (Lam var ki body')
dmdAnal' env dmd (Case scrut case_bndr ty [Alt alt_con bndrs rhs])
  | want_precise_field_dmds alt_con
  = let rhs_env = addInScopeAnalEnvs env (case_bndr:bndrs)

        WithDmdType rhs_ty rhs' = dmdAnal rhs_env dmd rhs
        WithDmdType alt_ty1 fld_dmds = findBndrsDmds env rhs_ty bndrs
        WithDmdType alt_ty2 case_bndr_dmd = findBndrDmd env alt_ty1 case_bndr
        !case_bndr' = setIdDemandInfo case_bndr case_bndr_dmd

        (_ :* case_bndr_sd) = case_bndr_dmd

        !(!bndrs', !scrut_sd)
          | DataAlt _ <- alt_con
          , let !scrut_sd = scrutSubDmd case_bndr_sd fld_dmds
          , let !fld_dmds' = fieldBndrDmds scrut_sd (length fld_dmds)
          , let !bndrs' = setBndrsDemandInfo bndrs fld_dmds'
          = (bndrs', scrut_sd)
          | otherwise
          = assert (null bndrs) (panic "empty case")

        alt_ty3 = alt_ty2 -- TODO: precise exceptions?

        WithDmdType scrut_ty scrut' = dmdAnal env scrut_sd scrut
        res_ty = alt_ty2 `plusDmdType` discardArgDmds scrut_ty
    in WithDmdType res_ty (Case scrut' case_bndr' ty [Alt alt_con bndrs' rhs'])
  where
    want_precise_field_dmds (DataAlt dc)
      | Nothing <- tyConSingleAlgDataCon_maybe $ dataConTyCon dc
      = False
      -- TODO: recursive types mu
      | otherwise
      = True
    want_precise_field_dmds LitAlt{} = False
    want_precise_field_dmds DEFAULT = True

dmdAnal' env dmd (Case scrut case_bndr ty alts)
  = let WithDmdType scrut_ty scrut' = dmdAnal env topSubDmd scrut
        WithDmdType alt_ty1 case_bndr_dmd = findBndrDmd env alt_ty case_bndr
        !case_bndr' = setIdDemandInfo case_bndr case_bndr_dmd
        WithDmdType alt_ty alts' = dmdAnalSumAlts env dmd case_bndr alts
        alt_ty2
          -- TODO: precise exception
          = alt_ty1
        res_ty = scrut_ty `plusDmdType` discardArgDmds alt_ty2
    in WithDmdType res_ty (Case scrut' case_bndr' ty alts')

dmdAnal' env dmd (Let bind body)
  = WithDmdType final_ty (Let bind' body')
  where
    !(WithDmdType final_ty (R bind' body')) = dmdAnalBind NotTopLevel env dmd bind go'
    go' !env' = dmdAnal env' dmd body

dmdAnalSumAlts :: AnalEnv -> SubDemand -> CoreId -> [CoreAlt] -> WithDmdType [CoreAlt]
dmdAnalSumAlts _ _ _ [] = WithDmdType botDmdType []
dmdAnalSumAlts env dmd case_bndr (alt : alts)
  = let WithDmdType cur_ty alt' = dmdAnalSumAlt env dmd case_bndr alt
        WithDmdType rest_ty alts' = dmdAnalSumAlts env dmd case_bndr alts
    in WithDmdType (lubDmdType cur_ty rest_ty) (alt':alts')

dmdAnalSumAlt :: AnalEnv -> SubDemand -> CoreId -> CoreAlt -> WithDmdType CoreAlt
dmdAnalSumAlt env dmd case_bndr (Alt con bndrs rhs)
  = let rhs_env = addInScopeAnalEnvs env (case_bndr:bndrs)
        WithDmdType rhs_ty rhs' = dmdAnal rhs_env dmd rhs
        WithDmdType alt_ty dmds = findBndrsDmds env rhs_ty bndrs
        (_ :* case_bndr_sd) = findIdDemand alt_ty case_bndr
        scrut_sd = scrutSubDmd case_bndr_sd dmds
        dmds' = fieldBndrDmds scrut_sd (length dmds)
        !new_ids = setBndrsDemandInfo bndrs dmds'
    in WithDmdType alt_ty (Alt con new_ids rhs')

scrutSubDmd :: SubDemand -> [Demand] -> SubDemand
scrutSubDmd case_sd fld_dmds
  = case_sd `plusSubDmd` mkProd fld_dmds

fieldBndrDmds :: SubDemand -> Arity -> [Demand]
fieldBndrDmds scrut_sd n_flds = case viewProd n_flds scrut_sd of
                                  Just ds -> ds
                                  Nothing -> replicate n_flds topDmd

{- *********************************************************************
*                                                                      *
          Demand transformer
*                                                                      *
********************************************************************* -}

dmdTransform
  :: AnalEnv
  -> CoreId
  -> SubDemand
  -> DmdType
dmdTransform env var sd
  | Just con <- isDataConId_maybe var
  = dmdTransformDataConSig (dataConArity con) sd
  | isGlobalId var
  = dmdTransformSig (idDmdSig var) sd
  | Just (sig, top_lvl) <- lookupSigEnv env var
  = let fn_ty = dmdTransformSig sig sd
    in case top_lvl of
         NotTopLevel -> addVarDmd fn_ty var (C_11 :* sd)
         TopLevel | isInterestingTopLevelFn var
                    -> addVarDmd fn_ty var (floatifyDmd (C_11 :* sd))
                  | otherwise
                    -> fn_ty
  | otherwise
  = noArgsDmdType (addVarDmdEnv nopDmdEnv var (C_11 :* sd))

{- *********************************************************************
*                                                                      *
                      Binding right-hand sides
*                                                                      *
********************************************************************* -}

dmdAnalRhsSig
  :: TopLevelFlag
  -> RecFlag
  -> AnalEnv
  -> SubDemand
  -> CoreId
  -> CoreExpr
  -> (AnalEnv, CoreId, CoreExpr)
dmdAnalRhsSig top_lvl rec_flag env let_sd id rhs
  = (final_env, final_id, final_rhs)
  where
    arity = case idJoinPointHood id of
      JoinPoint join_arity -> count (isRuntimeVar . fst) $ fst $ collectNBinders join_arity rhs
      NotJoinPoint -> idArity id

    body_sd | isJoinId id = let_sd
            | otherwise = topSubDmd

    rhs_sd = mkCalledOnceDmds arity body_sd

    WithDmdType rhs_dmd_ty rhs' = dmdAnal env rhs_sd rhs
    DmdType rhs_env rhs_dmds = rhs_dmd_ty
    (final_rhs_dmds, final_rhs) = (rhs_dmds, rhs')

    dmd_sig_arity = arity + strictCallArity body_sd
    sig = mkDmdSigForArity dmd_sig_arity (DmdType sig_env final_rhs_dmds)

    final_id = setIdDmdSig id sig
    !final_env = extendAnalEnv top_lvl env final_id sig

    rhs_env1 = case rec_flag of
      Recursive -> reuseEnv rhs_env
      NonRecursive -> rhs_env

    rhs_env2 = rhs_env1 `plusDmdEnv` demandRootSet env (bndrRuleAndUnfoldingIds id)

    !sig_env = rhs_env2

useLetUp :: TopLevelFlag -> CoreId -> Bool
useLetUp top_lvl f = isNotTopLevel top_lvl && idArity f == 0 && not (isJoinId f)

{- *********************************************************************
*                                                                      *
                      Fixpoints
*                                                                      *
********************************************************************* -}

dmdFix
  :: TopLevelFlag
  -> AnalEnv
  -> SubDemand
  -> [(CoreId, CoreExpr)]
  -> (AnalEnv, [(CoreId, CoreExpr)])
dmdFix top_lvl env let_dmd orig_pairs
  = panic "loop 1 initial_pairs"
  -- where
  --   initial_pairs | ae_virgin env = [(setIdDmdSig' 

{- *********************************************************************
*                                                                      *
                 Strictness signatures and types
*                                                                      *
********************************************************************* -}

noArgsDmdType :: DmdEnv -> DmdType
noArgsDmdType dmd_env = DmdType dmd_env []

addVarDmd :: DmdType -> CoreId -> Demand -> DmdType
addVarDmd (DmdType fv ds) var dmd = DmdType (addVarDmdEnv fv var dmd) ds

setBndrsDemandInfo :: [CoreId] -> [Demand] -> [CoreId]
setBndrsDemandInfo (b:bs) (d:ds)
  = let !new_info = setIdDemandInfo b d
        !vars = setBndrsDemandInfo bs ds
    in new_info : vars
setBndrsDemandInfo [] ds = assert (null ds) []
setBndrsDemandInfo bs _ = pprPanic "setBndrsDemandInfo" (ppr bs)

annotateLamIdBndr :: AnalEnv -> DmdType -> CoreId -> WithDmdType CoreId
annotateLamIdBndr env dmd_ty id
  = WithDmdType main_ty new_id
  where
    new_id = setIdDemandInfo id dmd
    main_ty = addDemand dmd dmd_ty'
    WithDmdType dmd_ty' dmd = findBndrDmd env dmd_ty id

{- *********************************************************************
*                                                                      *
                 Strictness signatures 
*                                                                      *
********************************************************************* -}
    
data AnalEnv = AE
  { ae_sigs :: !SigEnv
  , ae_virgin :: !Bool
  }

type SigEnv = IdEnv Zk (DmdSig, TopLevelFlag)

instance Outputable AnalEnv where
  ppr env = text "AE" <+> braces (vcat [ text "ae_virgin =" <+> ppr (ae_virgin env)
                                       , text "ae_sigs =" <+> ppr (ae_sigs env)
                                       ])

emptyAnalEnv :: AnalEnv
emptyAnalEnv = AE { ae_sigs = emptySigEnv, ae_virgin = True }

emptySigEnv :: SigEnv
emptySigEnv = emptyVarEnv

extendAnalEnv :: TopLevelFlag -> AnalEnv -> CoreId -> DmdSig -> AnalEnv
extendAnalEnv top_lvl env var sig
  = env { ae_sigs = extendSigEnv top_lvl (ae_sigs env) var sig }

extendSigEnv :: TopLevelFlag -> SigEnv -> CoreId -> DmdSig -> SigEnv
extendSigEnv top_lvl sigs var sig = extendVarEnv sigs var (sig, top_lvl)

lookupSigEnv :: AnalEnv -> CoreId -> Maybe (DmdSig, TopLevelFlag)
lookupSigEnv env id = lookupVarEnv (ae_sigs env) id

addInScopeAnalEnv :: AnalEnv -> CoreId -> AnalEnv
addInScopeAnalEnv env id = env { ae_sigs = delVarEnv (ae_sigs env) id }

addInScopeAnalEnvs :: AnalEnv -> [CoreId] -> AnalEnv
addInScopeAnalEnvs env ids = env { ae_sigs = delVarEnvList (ae_sigs env) ids }

findBndrsDmds :: AnalEnv -> DmdType -> [CoreId] -> WithDmdType [Demand]
findBndrsDmds env dmd_ty bndrs
  = go dmd_ty bndrs
  where
    go dmd_ty [] = WithDmdType dmd_ty []
    go dmd_ty (b:bs) = let WithDmdType dmd_ty1 dmds = go dmd_ty bs
                           WithDmdType dmd_ty2 dmd = findBndrDmd env dmd_ty1 b
                       in WithDmdType dmd_ty2 (dmd : dmds)

findBndrDmd :: AnalEnv -> DmdType -> CoreId -> WithDmdType Demand
findBndrDmd env dmd_ty id
  = WithDmdType dmd_ty' dmd'
  where
    dmd' = trimToType starting_dmd (findTypeShape id_ty)

    (dmd_ty', starting_dmd) = peelFV dmd_ty id

    id_ty = varType id
