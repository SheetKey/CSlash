{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module CSlash.Core.Opt.FloatIn (floatInwards) where

import Prelude hiding ((<>))

import CSlash.Platform
import CSlash.Cs.Pass

import CSlash.Core as C
import CSlash.Core.Opt.Arity( isOneShotBndr )
import CSlash.Core.Make hiding ( wrapFloats )
import CSlash.Core.Utils
import CSlash.Core.FVs
import CSlash.Core.Type

import CSlash.Types.Basic ( RecFlag(..), isRec )
import CSlash.Types.Var.Id ( isJoinId, idJoinPointHood )
import CSlash.Types.Tickish
import CSlash.Types.Var
import CSlash.Types.Var.Set

import CSlash.Utils.Misc
import CSlash.Utils.Panic.Plain

import CSlash.Utils.Outputable

import Data.List ( mapAccumL )

floatInwards :: Platform -> CoreProgram -> CoreProgram
floatInwards platform binds = map (fi_top_bind platform) binds
  where
    fi_top_bind platform (NonRec binder rhs)
      = NonRec binder (fiExpr platform [] (freeVars rhs))
    fi_top_bind platform (Rec pairs)
      = Rec [(b, fiExpr platform [] (freeVars rhs)) | (b, rhs) <- pairs]

{- *********************************************************************
*                                                                      *
               Main floating-inwards code
*                                                                      *
********************************************************************* -}

type FreeVarSet = DCoreVarSets
type BoundVarSet = DIdSet Zk

data FloatInBind = FB BoundVarSet FreeVarSet FloatBind

type FloatInBinds = [FloatInBind]
type RevFloatInBinds = [FloatInBind]

instance Outputable FloatInBind where
  ppr (FB bvs fvs _) = text "FB" <> braces (sep [ text "bndrs =" <+> ppr bvs
                                                , text "fvs =" <+> ppr fvs ])

fiExpr
  :: Platform
  -> RevFloatInBinds
  -> CoreExprWithFVs
  -> CoreExpr
fiExpr _ to_drop (_, AnnLit lit) = wrapFloats to_drop (Lit lit)
fiExpr _ to_drop (_, AnnVar v) = wrapFloats to_drop (Var v)
fiExpr _ to_drop (_, AnnType ty) = assert (null to_drop) $ Type ty
fiExpr _ to_drop (_, AnnKiCo co) = assert (null to_drop) $ KiCo co
fiExpr _ to_drop (_, AnnKind ki) = assert (null to_drop) $ Kind ki

fiExpr platform to_drop (_, AnnCast expr (co_ann, co))
  = wrapFloats drop_here $
    Cast (fiExpr platform e_drop expr) co
  where
    (drop_here, [e_drop]) = sepBindsByDropPoint platform False to_drop
                          co_ann [freeVarsOf expr]

fiExpr platform to_drop ann_expr@(_, AnnApp {})
  = wrapFloats drop_here $
    mkTicks ticks $
    mkCoreApps (fiExpr platform fun_drop ann_fun)
           (zipWithEqual "fiExpr" (fiExpr platform) arg_drops ann_args)
  where
    (ann_fun, ann_args, ticks) = collectAnnArgsTicks tickishFloatable ann_expr
    fun_fvs = freeVarsOf ann_fun

    (drop_here, fun_drop : arg_drops)
      = sepBindsByDropPoint platform False to_drop here_fvs (fun_fvs : arg_fvs)

    (here_fvs, arg_fvs) = mapAccumL add_arg here_fvs0 ann_args
    here_fvs0 = case ann_fun of
                  (_, AnnVar _) -> fun_fvs
                  _ -> emptyDCoreVarSets

    add_arg :: FreeVarSet -> CoreExprWithFVs -> (FreeVarSet, FreeVarSet)
    add_arg here_fvs (arg_fvs, arg)
      | noFloatIntoArg arg = (here_fvs `unionDCoreVarSets` arg_fvs, emptyDCoreVarSets)
      | otherwise = (here_fvs, arg_fvs)

fiExpr platform to_drop lam@(_, AnnLam _ _ _)
  | noFloatIntoLam (map fst bndrs)
  = wrapFloats to_drop (mkCoreLams bndrs (fiExpr platform [] body))
  | otherwise
  = wrapFloats drop_here $
    mkCoreLams bndrs (fiExpr platform body_drop body)
  where
    (bndrs, body) = collectAnnBndrs lam
    body_fvs = freeVarsOf body

    (drop_here, [body_drop]) = sepBindsByDropPoint platform False to_drop
                               (mkDCoreVarSetsBndrs $ map fst bndrs) [body_fvs]

fiExpr platform to_drop (_, AnnTick tickish expr)
  | tickish `tickishScopesLike` SoftScope
  = Tick tickish (fiExpr platform to_drop expr)

  | otherwise
  = wrapFloats to_drop (Tick tickish (fiExpr platform [] expr))

fiExpr platform to_drop (_, AnnLet bind body)
  = fiExpr platform (after ++ new_float : before) body
  where
    (before, new_float, after) = fiBind platform to_drop bind body_fvs
    body_fvs = freeVarsOf body

fiExpr platform to_drop (_, AnnCase scrut case_bndr _ [AnnAlt con alt_bndrs rhs])
  | exprOkToDiscard (deAnnotate scrut)
  = wrapFloats shared_binds $
    fiExpr platform (case_float : rhs_binds) rhs
  where
    case_float = FB all_bndrs scrut_fvs (FloatCase scrut' case_bndr con alt_bndrs)
    scrut' = fiExpr platform scrut_binds scrut
    rhs_fvs = freeVarsOf rhs
    scrut_fvs = freeVarsOf scrut
    all_bndrs = mkDVarSet alt_bndrs `extendDVarSet` case_bndr

    (shared_binds, [scrut_binds, rhs_binds])
      = sepBindsByDropPoint platform False to_drop
        (mkDCoreVarSetsDIdSet all_bndrs) [scrut_fvs, rhs_fvs]

fiExpr platform to_drop (_, AnnCase scrut case_bndr ty alts)
  = wrapFloats drop_here1 $
    wrapFloats drop_here2 $
    Case (fiExpr platform scrut_drops scrut) case_bndr ty
         (zipWithEqual "fiExpr" fi_alt alts_drops_s alts)

  where
    (drop_here1, [scrut_drops, alts_drops])
      = sepBindsByDropPoint platform False to_drop
        all_alt_bndrs [scrut_fvs, all_alt_fvs]

    (drop_here2, alts_drops_s)
      = sepBindsByDropPoint platform True alts_drops emptyDCoreVarSets alts_fvs

    scrut_fvs = freeVarsOf scrut

    all_alt_bndrs = foldr (unionDCoreVarSets . ann_alt_bndrs) (unitDCoreVarSets case_bndr) alts
    ann_alt_bndrs (AnnAlt _ bndrs _) = mkDCoreVarSets bndrs

    alts_fvs :: [DCoreVarSets]
    alts_fvs = [freeVarsOf rhs | AnnAlt _ _ rhs <- alts]

    all_alt_fvs :: DCoreVarSets
    all_alt_fvs = foldr unionDCoreVarSets (unitDCoreVarSets case_bndr) alts_fvs

    fi_alt to_drop (AnnAlt con args rhs) = Alt con args (fiExpr platform to_drop rhs)

fiBind
  :: Platform
  -> RevFloatInBinds
  -> CoreBindWithFVs
  -> DCoreVarSets
  -> (RevFloatInBinds, FloatInBind, RevFloatInBinds)

fiBind platform to_drop (AnnNonRec id ann_rhs@(rhs_fvs, rhs)) body_fvs
  = ( shared_binds
    , FB (unitDVarSet id) rhs_fvs' (FloatLet (NonRec id rhs'))
    , body_binds)
  where
    body_fvs2 = body_fvs `delDCoreVarSet` id

    rule_fvs = bndrRuleAndUnfoldingVarsDSet id
    extra_fvs | noFloatIntoRhs NonRecursive id rhs
              = rule_fvs `unionDCoreVarSets` rhs_fvs
              | otherwise
              = rule_fvs

    (shared_binds, [rhs_binds, body_binds])
      = sepBindsByDropPoint platform False to_drop extra_fvs [rhs_fvs, body_fvs2]

    rhs' = fiRhs platform rhs_binds id ann_rhs
    rhs_fvs' = rhs_fvs `unionDCoreVarSets` floatedBindsFVs rhs_binds
                       `unionDCoreVarSets` rule_fvs

fiBind platform to_drop (AnnRec bindings) body_fvs
  = ( shared_binds
    , FB (mkDVarSet ids) rhs_fvs' (FloatLet (Rec (fi_bind rhss_binds bindings)))
    , body_binds )
  where
    (ids, rhss) = unzip bindings
    rhss_fvs = map freeVarsOf rhss

    rule_fvs = mapUnionDCoreVarSets bndrRuleAndUnfoldingVarsDSet ids
    extra_fvs = rule_fvs `unionDCoreVarSets`
                unionListDCoreVarSets [ rhs_fvs | (bndr, (rhs_fvs, rhs)) <- bindings
                                                , noFloatIntoRhs Recursive bndr rhs ]

    (shared_binds, body_binds : rhss_binds)
      = sepBindsByDropPoint platform False to_drop extra_fvs (body_fvs : rhss_fvs)

    rhs_fvs' = unionListDCoreVarSets rhss_fvs `unionDCoreVarSets`
               unionListDCoreVarSets (map floatedBindsFVs rhss_binds) `unionDCoreVarSets`
               rule_fvs

    fi_bind :: [RevFloatInBinds] -> [(CoreId, CoreExprWithFVs)] -> [(CoreId, CoreExpr)]
    fi_bind to_drops pairs
      = [ (binder, fiRhs platform to_drop binder rhs)
        | ((binder, rhs), to_drop) <- zipEqual "fi_bind" pairs to_drops ]

fiRhs :: Platform -> RevFloatInBinds -> CoreId -> CoreExprWithFVs -> CoreExpr
fiRhs platform to_drop bndr rhs
  | JoinPoint join_arity <- idJoinPointHood bndr
  = let (bndrs, body) = collectNAnnBndrs join_arity rhs
    in mkCoreLams bndrs (fiExpr platform to_drop body)
  | otherwise
  = fiExpr platform to_drop rhs

noFloatIntoLam :: [CoreBndr] -> Bool
noFloatIntoLam bndrs = any bad bndrs
  where
    bad b@(C.Id _) = not (isOneShotBndr b)
    bad _ = False

noFloatIntoRhs :: RecFlag -> CoreId -> CoreExprWithFVs' -> Bool
noFloatIntoRhs is_rec bndr rhs
  | isJoinId bndr
  = isRec is_rec

  -- TODO: verify let-can-float invariant in mkCoreLet!
  -- Add comments about this in Core:
  -- 'let' is only different from case because let-can-float
  | otherwise
  = True -- all types are unlifted

noFloatIntoArg :: CoreExprWithFVs' -> Bool
noFloatIntoArg expr
  | AnnLam bndr ki e <- expr
  , (bndrs, _) <- collectAnnBndrs e
  = noFloatIntoLam (bndr : map fst bndrs)
    || all isNonRuntimeVar (bndr : map fst bndrs)

  | otherwise
  = exprIsTrivial deann_expr || exprIsHNF deann_expr
  where
    deann_expr = deAnnotate' expr

{- *********************************************************************
*                                                                      *
             sepBindsByDropPoint
*                                                                      *
********************************************************************* -}

type DropBox = (FreeVarSet, FloatInBinds)

dropBoxFloats :: DropBox -> RevFloatInBinds
dropBoxFloats (_, floats) = reverse floats

usedInDropBox :: DIdSet Zk -> DropBox -> Bool
usedInDropBox bndrs ((db_fvs, _, _, _, _), _) = db_fvs `intersectsDVarSet` bndrs

initDropBox :: FreeVarSet -> DropBox
initDropBox fvs = (fvs, [])

sepBindsByDropPoint
  :: Platform
  -> Bool
  -> RevFloatInBinds
  -> FreeVarSet
  -> [FreeVarSet]
  -> (RevFloatInBinds, [RevFloatInBinds])
sepBindsByDropPoint platform is_case floaters here_fvs fork_fvs
  | null floaters
  = ([], [[] | _ <- fork_fvs])

  | otherwise
  = go floaters (initDropBox here_fvs) (map initDropBox fork_fvs)

  where
    n_alts = length fork_fvs

    go :: RevFloatInBinds -> DropBox -> [DropBox] -> (RevFloatInBinds, [RevFloatInBinds])
    go [] here_box fork_boxes
      = (dropBoxFloats here_box, map dropBoxFloats fork_boxes)
    go (bind_w_fvs@(FB bndrs bind_fvs bind) : binds) here_box fork_boxes
      | drop_here = go binds (insert here_box) fork_boxes
      | otherwise = go binds here_box new_fork_boxes
      where
        used_here = bndrs `usedInDropBox` here_box
        used_in_flags = case fork_boxes of
                          [] -> []
                          [_] -> [True]
                          _ -> map (bndrs `usedInDropBox`) fork_boxes

        drop_here = used_here || cant_push

        n_used_alts = count id used_in_flags

        cant_push
          | is_case = (n_alts > 1 && n_used_alts == n_alts)
                      || (n_used_alts > 1 && not (floatIsDupable platform bind))
          | otherwise = floatIsCase bind || n_used_alts > 1

        new_fork_boxes = zipWithEqual "FloatIn.sepBinds" insert_maybe fork_boxes used_in_flags

        insert (fvs, drops) = (fvs `unionDCoreVarSets` bind_fvs, bind_w_fvs : drops)

        insert_maybe box True = insert box
        insert_maybe box False = box

floatedBindsFVs :: RevFloatInBinds -> FreeVarSet
floatedBindsFVs binds = mapUnionDCoreVarSets fbFVs binds

fbFVs :: FloatInBind -> FreeVarSet
fbFVs (FB _ fvs _) = fvs

wrapFloats :: RevFloatInBinds -> CoreExpr -> CoreExpr
wrapFloats [] e = e
wrapFloats (FB _ _ fl : bs) e = wrapFloats bs (wrapFloat fl e)

floatIsDupable :: Platform -> FloatBind -> Bool
floatIsDupable platform (FloatCase scrut _ _ _) = exprIsDupable platform scrut
floatIsDupable platform (FloatLet (Rec prs)) = all (exprIsDupable platform . snd) prs
floatIsDupable platform (FloatLet (NonRec _ r)) = exprIsDupable platform r

floatIsCase :: FloatBind -> Bool
floatIsCase FloatCase{} = True
floatIsCase FloatLet{} = False
