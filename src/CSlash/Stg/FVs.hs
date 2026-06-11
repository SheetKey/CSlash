{-# LANGUAGE LambdaCase #-}

module CSlash.Stg.FVs (depSortWithAnnotStgPgm, annBindingFreeVars) where

import Prelude hiding (mod)

import CSlash.Core (CoreId)

import CSlash.Stg.Syntax
import CSlash.Stg.Utils (bindersOf)
import CSlash.Types.Var
import CSlash.Types.Var.Id
import CSlash.Types.Name (Name, nameIsLocalOrFrom)
import CSlash.Types.Tickish ( GenTickish(..) )
import CSlash.Types.Unique.Set (nonDetEltsUniqSet)
import CSlash.Types.Var.Set
import CSlash.Unit.Module (Module)
import CSlash.Utils.Misc
import CSlash.Utils.Panic

import Data.Graph (SCC (..))
import CSlash.Data.Graph.Directed( Node(..), stronglyConnCompFromEdgedVerticesUniq )

depSortWithAnnotStgPgm :: Module -> [StgTopBinding] -> [(CgStgTopBinding, ImpFVs)]
depSortWithAnnotStgPgm this_mod binds
  = {-# SCC "Stg.depSortWithAnnotStgPgm" #-}
    zip lit_binds (repeat emptyVarSet) ++ map from_scc sccs
  where
    (lit_binds, pairs) = flattenTopStgBindings binds

    nodes :: [Node Name (CoreId, CgStgRhs, ImpFVs)]
    nodes = map (annotateTopPair env0) pairs
    env0 = Env { locals = emptyVarSet, mod = this_mod }

    sccs :: [SCC (CoreId, CgStgRhs, ImpFVs)]
    sccs = stronglyConnCompFromEdgedVerticesUniq nodes

    from_scc = \case
      AcyclicSCC (bndr, rhs, imp_fvs) -> (StgTopBind (StgNonRec bndr rhs), imp_fvs)
      CyclicSCC triples -> (StgTopBind (StgRec pairs), imp_fvs)
        where
          (ids, rhss, imp_fvss) = unzip3 triples
          pairs = zip ids rhss
          imp_fvs = unionVarSets imp_fvss

flattenTopStgBindings :: [StgTopBinding] -> ([CgStgTopBinding], [(CoreId, StgRhs)])
flattenTopStgBindings binds
  = go [] [] binds
  where
    go lits pairs [] = (lits, pairs)
    go lits pairs (bind:binds)
      = case bind of
          StgTopStringLit {} -> panic "StgTopStringLit"
          StgTopBind stg_bind -> go lits (flatten_one stg_bind ++ pairs) binds

    flatten_one (StgNonRec b r) = [(b, r)]
    flatten_one (StgRec pairs) = pairs

annotateTopPair :: Env -> (CoreId, StgRhs) -> Node Name (CoreId, CgStgRhs, ImpFVs)
annotateTopPair env0 (bndr, rhs)
  = DigraphNode { node_key = varName bndr
                , node_payload = (bndr, rhs', imp_fvs)
                , node_dependencies = map varName (nonDetEltsUniqSet top_fvs) }
  where
    (rhs', imp_fvs, top_fvs, _) = rhsFVs env0 rhs

data Env = Env
  { locals :: CoreIdSet
  , mod :: Module
  }

addLocals :: [CoreId] -> Env -> Env
addLocals bndrs env = env { locals = extendVarSetList (locals env) bndrs }

type TopFVs = CoreIdSet
type ImpFVs = CoreIdSet
type LocalFVs = DCoreIdSet

annBindingFreeVars :: Module -> StgBinding -> CgStgBinding
annBindingFreeVars this_mod = fstOf4 . bindingFVs (Env emptyVarSet this_mod) emptyDVarSet

bindingFVs :: Env -> LocalFVs -> StgBinding -> (CgStgBinding, ImpFVs, TopFVs, LocalFVs)
bindingFVs env body_fv b = case b of
  StgNonRec bndr r -> (StgNonRec bndr r', imp_fvs, top_fvs, lcl_fvs)
    where
      (r', imp_fvs, top_fvs, rhs_lcl_fvs) = rhsFVs env r
      lcl_fvs = delDVarSet body_fv bndr `unionDVarSet` rhs_lcl_fvs

  StgRec pairs -> (StgRec pairs', imp_fvs, top_fvs, lcl_fvss)
    where
      bndrs = map fst pairs
      env' = addLocals bndrs env
      (rhss, rhs_imp_fvss, rhs_top_fvss, rhs_lcl_fvss) = mapAndUnzip4 (rhsFVs env' . snd) pairs
      top_fvs = unionVarSets rhs_top_fvss
      imp_fvs = unionVarSets rhs_imp_fvss
      pairs' = zip bndrs rhss
      lcl_fvss = delDVarSetList (unionDVarSets (body_fv : rhs_lcl_fvss)) bndrs
 
varFVs :: Env -> CoreId -> (ImpFVs, TopFVs, LocalFVs) -> (ImpFVs, TopFVs, LocalFVs)
varFVs env v (imp_fvs, top_fvs, lcl_fvs)
  | v `elemVarSet` locals env
  = (imp_fvs, top_fvs, lcl_fvs `extendDVarSet` v)
  | nameIsLocalOrFrom (mod env) (varName v)
  = (imp_fvs, top_fvs `extendVarSet` v, lcl_fvs)
  | otherwise
  = (imp_fvs `extendVarSet` v, top_fvs, lcl_fvs)

exprFVs :: Env -> StgExpr -> (CgStgExpr, ImpFVs, TopFVs, LocalFVs)
exprFVs env = go
  where
    go (StgApp f as)
      = let (imp_fvs, top_fvs, lcl_fvs) = varFVs env f (argsFVs env as)
        in (StgApp f as, imp_fvs, top_fvs, lcl_fvs)

    go (StgLit lit) = (StgLit lit, emptyVarSet, emptyVarSet, emptyDVarSet)

    go (StgConApp dc n as)
      = let (imp_fvs, top_fvs, lcl_fvs) = argsFVs env as
        in (StgConApp dc n as, imp_fvs, top_fvs, lcl_fvs)

    go (StgCase scrut bndr ty alts)
      = let (scrut', scrut_imp_fvs, scrut_top_fvs, scrut_lcl_fvs) = exprFVs env scrut
            (alts', alts_imp_fvss, alts_top_fvss, alts_lcl_fvss)
              = mapAndUnzip4 (altFVs (addLocals [bndr] env)) alts
            top_fvs = scrut_top_fvs `unionVarSet` unionVarSets alts_top_fvss
            imp_fvs = scrut_imp_fvs `unionVarSet` unionVarSets alts_imp_fvss
            alts_lcl_fvs = unionDVarSets alts_lcl_fvss
            lcl_fvs = delDVarSet (unionDVarSet scrut_lcl_fvs alts_lcl_fvs) bndr
      in (StgCase scrut' bndr ty alts', imp_fvs, top_fvs, lcl_fvs)

    go (StgLet ext bind body) = go_bind (StgLet ext) bind body
    go (StgLetNoEscape ext bind body) = go_bind (StgLetNoEscape ext) bind body

    go (StgTick tick e)
      = let (e', imp_fvs, top_fvs, lcl_fvs) = exprFVs env e
            lcl_fvs' = unionDVarSet (tickish tick) lcl_fvs
        in (StgTick tick e', imp_fvs, top_fvs, lcl_fvs')
      where tickish CpcTick{} = emptyDVarSet

    go_bind dc bind body = (dc bind' body', imp_fvs, top_fvs, lcl_fvs)
      where
        env' = addLocals (bindersOf bind) env
        (body', body_imp_fvs, body_top_fvs, body_lcl_fvs) = exprFVs env' body
        (bind', bind_imp_fvs, bind_top_fvs, lcl_fvs) = bindingFVs env' body_lcl_fvs bind
        top_fvs = bind_top_fvs `unionVarSet` body_top_fvs
        imp_fvs = bind_imp_fvs `unionVarSet` body_imp_fvs

rhsFVs :: Env -> StgRhs -> (CgStgRhs, ImpFVs, TopFVs, LocalFVs)
rhsFVs env (StgRhsClosure _ bs body ty)
  = let (body', imp_fvs, top_fvs, lcl_fvs) = exprFVs (addLocals bs env) body
        lcl_fvs' = delDVarSetList lcl_fvs bs
    in (StgRhsClosure lcl_fvs' bs body' ty, imp_fvs, top_fvs, lcl_fvs')
rhsFVs env (StgRhsCon dc mu ts bs ty)
  = let (imp_fvs, topp_fvs, lcl_fvs) = argsFVs env bs
    in (StgRhsCon dc mu ts bs ty, imp_fvs, topp_fvs, lcl_fvs)

argsFVs :: Env -> [StgArg] -> (ImpFVs, TopFVs, LocalFVs)
argsFVs env = foldl' f (emptyVarSet, emptyVarSet, emptyDVarSet)
  where
    f fvs StgLitArg{} = fvs
    f fvs (StgVarArg v) = varFVs env v fvs

altFVs :: Env -> StgAlt -> (CgStgAlt, ImpFVs, TopFVs, LocalFVs)
altFVs env GenStgAlt{ alt_con = con, alt_bndrs = bndrs, alt_rhs = e }
  = let (e', imp_fvs, top_fvs, lcl_fvs) = exprFVs (addLocals bndrs env) e
        lcl_fvs' = delDVarSetList lcl_fvs bndrs
        newAlt = GenStgAlt{ alt_con = con, alt_bndrs = bndrs, alt_rhs = e' }
    in (newAlt, imp_fvs, top_fvs, lcl_fvs')
