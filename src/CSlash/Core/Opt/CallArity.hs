{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Opt.CallArity (callArityAnalProgram, callArityRHS) where

import CSlash.Cs.Pass

import CSlash.Types.Var
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env

import CSlash.Types.Basic
import CSlash.Core as C
import CSlash.Types.Var.Id
import CSlash.Core.Opt.Arity ( typeArity )
import CSlash.Core.Utils ( exprIsCheap, exprIsTrivial )
import CSlash.Data.Graph.UnVar
import CSlash.Types.Demand
import CSlash.Utils.Misc
import CSlash.Utils.Panic

import Control.Arrow ( first, second )

{- *********************************************************************
*                                                                      *
               Call Arity Analysis
*                                                                      *
********************************************************************* -}

callArityAnalProgram :: CoreProgram -> CoreProgram
callArityAnalProgram binds = binds'
  where
    (_, binds') = callArityTopLvl [] emptyVarSet binds

callArityTopLvl :: [CoreId] -> CoreIdSet -> [CoreBind] -> (CallArityRes, [CoreBind])
callArityTopLvl exported _ []
  = ( calledMultipleTimes $ (emptyUnVarGraph, mkVarEnv $ [(v, 0) | v <- exported])
    , [] )

callArityTopLvl exported int1 (b:bs)
  = (ae2, b':bs')
  where
    int2 = bindersOf b
    exported' = filter isExportedId int2 ++ exported
    int' = int1 `addInterestingBinds` b
    (ae1, bs') = callArityTopLvl exported' int' bs
    (ae2, b') = callArityBind (boringBinds b) ae1 int1 b

callArityRHS :: CoreExpr -> CoreExpr
callArityRHS = snd . callArityAnal 0 emptyVarSet

callArityAnal
  :: Arity
  -> CoreIdSet
  -> CoreExpr
  -> (CallArityRes, CoreExpr)
callArityAnal _ _ e@Lit{} = (emptyArityRes, e)
callArityAnal _ _ e@Type{} = (emptyArityRes, e)
callArityAnal _ _ e@KiCo{} = (emptyArityRes, e)
callArityAnal _ _ e@Kind{} = (emptyArityRes, e)

callArityAnal arity int (Tick t e)
  = second (Tick t) $ callArityAnal arity int e
callArityAnal arity int (Cast e co)
  = second (flip Cast co) $ callArityAnal arity int e

callArityAnal arity int e@(Var v)
  | v `elemVarSet` int
  = (unitArityRes v arity, e)
  | otherwise
  = (emptyArityRes, e)

callArityAnal arity int (Lam v k e)
  | isNonRuntimeVar v
  = second (Lam v k) $ callArityAnal arity int e

callArityAnal 0 int (Lam b@(C.Id v) k e)
  = (ae', Lam b k e')
  where
    (ae, e') = callArityAnal 0 (int `delVarSet` v) e
    ae' = calledMultipleTimes ae

callArityAnal arity int (Lam b@(C.Id v) k e)
  = (ae, Lam b k e')
  where
    (ae, e') = callArityAnal (arity - 1) (int `delVarSet` v) e

callArityAnal _ _ (Lam _ _ _) = panic "unreachable:satisfy non-exhaustive warning"

callArityAnal arity int (App e (Type t))
  = second (\e -> App e (Type t)) $ callArityAnal arity int e

callArityAnal arity int (App e (KiCo c))
  = second (\e -> App e (KiCo c)) $ callArityAnal arity int e

callArityAnal arity int (App e (Kind k))
  = second (\e -> App e (Kind k)) $ callArityAnal arity int e

callArityAnal arity int (App e1 e2)
  = (final_ae, App e1' e2')
  where
    (ae1, e1') = callArityAnal (arity + 1) int e1
    (ae2, e2') = callArityAnal 0 int e2
    ae2' | exprIsTrivial e2 = calledMultipleTimes ae2
         | otherwise = ae2
    final_ae = ae1 `both` ae2'

callArityAnal arity int (Case scrut bndr ty alts)
  = (final_ae, Case scrut' bndr ty alts')
  where
    (alt_aes, alts') = unzip $ map go alts
    go (Alt dc bndrs e)
      = let (ae, e') = callArityAnal arity (int `delVarSetList` (bndr:bndrs)) e
        in (ae, Alt dc bndrs e')
    alt_ae = lubRess alt_aes
    (scrut_ae, scrut') = callArityAnal 0 int scrut
    final_ae = scrut_ae `both` alt_ae

callArityAnal arity int (Let bind e)
  = (final_ae, Let bind' e')
  where
    int_body = int `addInterestingBinds` bind
    (ae_body, e') = callArityAnal arity int_body e
    (final_ae, bind') = callArityBind (boringBinds bind) ae_body int bind

isInteresting :: CoreId -> Bool
isInteresting v = typeArity (varType v) > 0

interestingBinds :: CoreBind -> [CoreId]
interestingBinds = filter isInteresting . bindersOf

boringBinds :: CoreBind -> CoreIdSet
boringBinds = mkVarSet . filter (not . isInteresting) . bindersOf

addInterestingBinds :: CoreIdSet -> CoreBind -> CoreIdSet
addInterestingBinds int bind
  = int `delVarSetList` bindersOf bind
        `extendVarSetList` interestingBinds bind

callArityBind
  :: CoreIdSet
  -> CallArityRes
  -> CoreIdSet
  -> CoreBind
  -> (CallArityRes, CoreBind)
callArityBind boring_vars ae_body int (NonRec v rhs)
  = (final_ae, NonRec v' rhs')
  where
    not_cheap = not (exprIsCheap rhs)
    boring = v `elemVarSet` boring_vars

    (arity, called_once)
      | boring = (0, False)
      | otherwise = lookupCallArityRes ae_body v
    safe_arity | called_once = arity
               | not_cheap = 0
               | otherwise = arity

    trimmed_arity = trimArity v safe_arity

    (ae_rhs, rhs') = callArityAnal trimmed_arity int rhs

    ae_rhs' | called_once = ae_rhs
            | safe_arity == 0 = ae_rhs
            | otherwise = calledMultipleTimes ae_rhs

    called_by_v = domRes ae_rhs'
    called_with_v | boring = domRes ae_body
                  | otherwise = calledWith ae_body v `delUnVarSet` v

    final_ae = addCrossCoCalls called_by_v called_with_v $ ae_rhs' `lubRes` resDel v ae_body

    v' = v `setIdCallArity` trimmed_arity

callArityBind boring_vars ae_body int b@(Rec binds)
  = (final_ae, Rec  binds')
  where
    any_boring = any (`elemVarSet` boring_vars) (map fst binds)

    int_body = int `addInterestingBinds` b
    (ae_rhs, binds') = fix initial_binds
    final_ae = bindersOf b `resDelList` ae_rhs

    initial_binds = [(i, Nothing, e) | (i, e) <- binds]

    fix
      :: [(CoreId, Maybe (Bool, Arity, CallArityRes), CoreExpr)]
      -> (CallArityRes, [(CoreId, CoreExpr)])
    fix ann_binds
      | any_change
      = fix ann_binds'
      | otherwise
      = (ae, map (\(i, _, e) -> (i, e)) ann_binds')
      where
        aes_old = [(i, ae) | (i, Just (_, _, ae), _) <- ann_binds]
        ae = callArityRecEnv any_boring aes_old ae_body

        rerun (i, mbLastRun, rhs)
          | i `elemVarSet` int_body && not (i `elemUnVarSet` domRes ae)
          = (False, (i, Nothing, rhs))

          | Just (old_called_once, old_arity, _) <- mbLastRun
          , called_once == old_called_once
          , new_arity == old_arity
          = (False, (i, mbLastRun, rhs))

          | otherwise
          = let not_cheap = not (exprIsCheap rhs)
                safe_arity | not_cheap = 0 -- TODO: Maybe we don't care about duping/sharing work in the same way. Test compiler without these checks!
                           | otherwise = new_arity

                trimmed_arity = trimArity i safe_arity

                (ae_rhs, rhs') = callArityAnal trimmed_arity int_body rhs

                ae_rhs' | called_once = ae_rhs
                        | safe_arity == 0 = ae_rhs
                        | otherwise = calledMultipleTimes ae_rhs

                i' = i `setIdCallArity` trimmed_arity

            in (True, (i', Just (called_once, new_arity, ae_rhs'), rhs'))

          where
            (new_arity, called_once) | i `elemVarSet` boring_vars = (0, False)
                                     | otherwise = lookupCallArityRes ae i

        (changes, ann_binds') = unzip $ map rerun ann_binds

        any_change = or changes

callArityRecEnv :: Bool -> [(CoreId, CallArityRes)] -> CallArityRes -> CallArityRes
callArityRecEnv any_boring ae_rhss ae_body
  = ae_new
  where
    vars = map fst ae_rhss

    ae_combined = lubRess (map snd ae_rhss) `lubRes` ae_body

    cross_calls
      | any_boring = completeGraph (domRes ae_combined)
      | lengthExceeds ae_rhss 25 = completeGraph (domRes ae_combined)
      | otherwise = unionUnVarGraphs $ map cross_call ae_rhss

    cross_call (v, ae_rhs) = completeBipartiteGraph called_by_v called_with_v
      where
        not_cheap = idCallArity v == 0

        ae_before_v | not_cheap = lubRess (map snd $ filter ((/= v) . fst) ae_rhss)
                                  `lubRes` ae_body
                    | otherwise = ae_combined

        called_with_v = unionUnVarSets $ map (calledWith ae_before_v) vars
        called_by_v = domRes ae_rhs

    ae_new = first (cross_calls `unionUnVarGraph`) ae_combined

trimArity :: CoreId -> Arity -> Arity
trimArity v a = minimum [a, max_arity_by_type, max_arity_by_strsig]
  where
    max_arity_by_type = typeArity (varType v)
    max_arity_by_strsig
      | isDeadEndDiv result_info = length demands
      | otherwise = a
    (demands, result_info) = splitDmdSig (idDmdSig v)

---------------------------------------
-- Functions related to CallArityRes --
---------------------------------------

type CallArityRes = (UnVarGraph, IdEnv Zk Arity)

emptyArityRes :: CallArityRes
emptyArityRes = (emptyUnVarGraph, emptyVarEnv)

unitArityRes :: CoreId -> Arity -> CallArityRes
unitArityRes v arity = (emptyUnVarGraph, unitVarEnv v arity)

resDelList :: [CoreId] -> CallArityRes -> CallArityRes
resDelList vs ae = foldl' (flip resDel) ae vs

resDel :: CoreId -> CallArityRes -> CallArityRes
resDel v (!g, !ae) = (g `delNode` v, ae `delVarEnv` v)

domRes :: CallArityRes -> UnVarSet
domRes (_, ae) = varEnvDomain ae

lookupCallArityRes :: CallArityRes -> CoreId -> (Arity, Bool)
lookupCallArityRes (g, ae) v
  = case lookupVarEnv ae v of
      Just a -> (a, not (g `hasLoopAt` v))
      Nothing -> (0, False)

calledWith :: CallArityRes -> CoreId -> UnVarSet
calledWith (g, _) v = neighbors g v

addCrossCoCalls :: UnVarSet -> UnVarSet -> CallArityRes -> CallArityRes
addCrossCoCalls set1 set2 = first (completeBipartiteGraph set1 set2 `unionUnVarGraph`)

calledMultipleTimes :: CallArityRes -> CallArityRes
calledMultipleTimes res = first (const (completeGraph (domRes res))) res

both :: CallArityRes -> CallArityRes -> CallArityRes
both r1 r2 = addCrossCoCalls (domRes r1) (domRes r2) $ r1 `lubRes` r2

lubRes :: CallArityRes -> CallArityRes -> CallArityRes
lubRes (g1, ae1) (g2, ae2) = (g1 `unionUnVarGraph` g2, ae1 `lubArityEnv` ae2)

lubArityEnv :: IdEnv Zk Arity -> IdEnv Zk Arity -> IdEnv Zk Arity
lubArityEnv = plusVarEnv_C min

lubRess :: [CallArityRes] -> CallArityRes
lubRess = foldl' lubRes emptyArityRes
