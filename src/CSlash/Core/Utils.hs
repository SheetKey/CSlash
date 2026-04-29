module CSlash.Core.Utils where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Platform

import CSlash.Core as Core
import CSlash.Core.Ppr
-- import GHC.Core.FVs( bindFreeVars )
import CSlash.Core.DataCon
import CSlash.Core.Type as Type
-- import GHC.Core.Predicate( isEqPred )
import CSlash.Core.Type.Compare( eqType )
-- import GHC.Core.Coercion
-- import CSlash.Core.Reduction
import CSlash.Core.TyCon
import CSlash.Core.Kind

import CSlash.Types.Var
import CSlash.Types.SrcLoc
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Name
import CSlash.Types.Literal
import CSlash.Types.Tickish
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.Basic( Arity )
import CSlash.Types.Unique
import CSlash.Types.Unique.Set
import CSlash.Types.Demand
-- import CSlash.Types.RepType (isZeroBitTy)

import CSlash.Data.FastString
import CSlash.Data.Maybe
import CSlash.Data.List.SetOps( minusList )
import CSlash.Data.OrdList

import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc
import CSlash.Utils.Trace

import Data.ByteString     ( ByteString )
import Data.Function       ( on )
import Data.List           ( sort, sortBy, partition, zipWith4, mapAccumL )
import qualified Data.List as Partial ( init, last )
import Data.Ord            ( comparing )
import Control.Monad       ( guard )
import qualified Data.Set as Set

{-**********************************************************************
*                                                                      *
           Type of a Core atom/expression
*                                                                      *
**********************************************************************-}

exprType :: HasDebugCallStack => CoreExpr -> CoreType 
exprType (Var var) = varType var
exprType (Lit lit) = literalType lit
exprType (Let bind body)
  | NonRec _ (Type _) <- bind
  = panic "exprType"
  | NonRec _ (KiCo _) <- bind
  = panic "exprType"
  | NonRec _ (Kind _) <- bind
  = panic "exprType"
  | otherwise = exprType body
exprType (Case _ _ ty _) = ty
exprType (Cast _ co) = tycoercionRType co
exprType (Tick _ e) = exprType e
exprType (Lam bndr mki expr) = mkLamType bndr mki (exprType expr)
exprType e@(App _ _) = case collectArgs e of
                        (fun, args) -> applyTypeToArgs (exprType fun) args
exprType (Type ty) = pprPanic "exprType" (ppr ty)
exprType (KiCo kco) = pprPanic "exprType" (ppr kco)
exprType (Kind ki) = pprPanic "exprType" (ppr ki)

mkLamTypes :: [(CoreBndr, Maybe CoreMonoKind)] -> CoreType -> CoreType
mkLamTypes vs ty = foldr (uncurry mkLamType) ty vs 

mkLamType :: HasDebugCallStack => CoreBndr -> Maybe CoreMonoKind -> CoreType -> CoreType 
mkLamType (Core.Id id) (Just ki) body_ty = mkFunctionType (varType id) ki body_ty
mkLamType (Tv tv) Nothing body_ty = mkForAllTy (Bndr tv coreTyLamForAllTyFlag) body_ty
mkLamType (KCv kcv) Nothing body_ty = mkForAllKiCo kcv body_ty
mkLamType (Kv kv) Nothing body_ty = mkBigLamTy kv body_ty
mkLamType bndr ki body = pprPanic "mkLamType bad CsLam"
                         $ vcat [ text "bndr" <+> ppr bndr
                                , text "maybe fun ki" <+> ppr ki
                                , text "body" <+> ppr body ]

applyTypeToArgs :: HasDebugCallStack => CoreType -> [CoreExpr] -> CoreType 
applyTypeToArgs op_ty args = go op_ty args
  where
    go op_ty [] = op_ty
    go op_ty (Type ty : args) = go_ty_args op_ty [ty] args
    go op_ty (KiCo co : args) = go_ty_args op_ty [KindCoercion co] args
    go op_ty (Kind ki : args) = go_ty_args op_ty [Embed ki] args
    go op_ty (_ : args) | Just (_, _, res_ty) <- splitFunTy_maybe op_ty
                        = go res_ty args
    go _ args = pprPanic "applyTypeToArgs" (panic_msg args)

    go_ty_args op_ty rev_tys (Type ty : args)
      = go_ty_args op_ty (ty : rev_tys) args
    go_ty_args op_ty rev_tys (KiCo co : args)
      = go_ty_args op_ty (KindCoercion co : rev_tys) args
    go_ty_args op_ty rev_tys (Kind ki : args)
      = go_ty_args op_ty (Embed ki : rev_tys) args
    go_ty_args op_ty rev_tys args = go (piResultTys op_ty (reverse rev_tys)) args

    panic_msg as = vcat [ text "Type:" <+> ppr op_ty
                        , text "Args:" <+> ppr args
                        , text "Args':" <+> ppr as ]

mkCastMCo :: CoreExpr -> Maybe (TypeCoercion Zk) -> CoreExpr
mkCastMCo e Nothing = e
mkCastMCo e (Just co) = Cast e co

{- *********************************************************************
*                                                                      *
             Casts
*                                                                      *
********************************************************************* -}

mkCast :: HasDebugCallStack => CoreExpr -> TypeCoercion Zk -> CoreExpr
mkCast expr co = warnPprTrace (not (tycoercionLType co `eqType` exprType expr))
                 "Trying to coerce" (parens (ppr expr
                                              $$ colon <+> ppr (exprType expr))
                                     $$ ppr co $$ ppr (tycoercionTypes co)
                                     $$ callStackDoc) $
                 case expr of
                   Cast expr co2 -> mkCast expr (mkTyTransCo co2 co)
                   Tick t expr -> Tick t (mkCast expr co)
                   KiCo _ -> panic "Casting a KiCo"
                   Kind _ -> panic "Casting a Kind"
                   _ | isReflTyCo co -> expr
                     | otherwise -> Cast expr co

{- *********************************************************************
*                                                                      *
             Attaching ticks
*                                                                      *
********************************************************************* -}

mkTick :: CoreTickish -> CoreExpr -> CoreExpr
mkTick t orig_expr = mkTick' id id orig_expr
  where
    canSplit = tickishCanSplit t && tickishPlace (mkNoCount t) /= tickishPlace t

    mkTick'
      :: (CoreExpr -> CoreExpr)
      -> (CoreExpr -> CoreExpr)
      -> CoreExpr -> CoreExpr
    mkTick' top rest expr = case expr of
      Tick t2 e
        | tickishPlace t2 /= tickishPlace t -> mkTick' (top . Tick t2) rest e
        | tickishContains t t2 -> mkTick' top rest e
        | tickishContains t2 t -> orig_expr
        | otherwise -> mkTick' top (rest . Tick t2) e

      Cast e co -> mkTick' (top . flip Cast co) rest e
      KiCo co -> KiCo co -- TODO: Why?

      Lam x mki e
        | not (isRuntimeVar x) || tickishPlace t /= PlaceRuntime
          -> mkTick' (top . Lam x mki) rest e
        | canSplit
          -> top $ Tick (mkNoScope t) $ rest $ Lam x mki $ mkTick (mkNoCount t) e

      App f arg
        | not (isRuntimeArg arg)
          -> mkTick' (top . flip App arg) rest f

        | isSaturatedConApp expr && canSplit -- TODO PlaceCostCentre
          -> top $ Tick (mkNoScope t) $ rest $ tickHNFArgs (mkNoCount t) expr

      Var x -- TODO PlaceCostCentre
        | notFunction && canSplit
          -> top $ Tick (mkNoScope t) $ rest expr
        where
          notFunction = not (isFunTy (varType x))

      _ -> top $ Tick t $ rest expr
      
mkTicks :: [CoreTickish] -> CoreExpr -> CoreExpr
mkTicks ticks expr = foldr mkTick expr ticks

isSaturatedConApp :: CoreExpr -> Bool
isSaturatedConApp e = go e []
  where
    go (App f a) as = go f (a:as)
    go (Var fun) args = isConLikeId fun && idArity fun == valArgCount args
    go (Cast f _) as = go f as
    go _ _ = False

tickHNFArgs :: CoreTickish -> CoreExpr -> CoreExpr
tickHNFArgs t e = push t e
  where
    push t (App f (Type u)) = App (push t f) (Type u)
    push t (App f (KiCo u)) = App (push t f) (KiCo u) -- TODO: check this
    push t (App f (Kind u)) = App (push t f) (Kind u)
    push t (App f arg) = App (push t f) (mkTick t arg)
    push _ e = e

stripTicksTop :: (CoreTickish -> Bool) -> Expr b1 b2 -> ([CoreTickish], Expr b1 b2)
stripTicksTop p = go []
  where go ts (Tick t e) | p t = go (t : ts) e
        go ts other = (reverse ts, other)

stripTicksTopE :: (CoreTickish -> Bool) -> Expr b1 b2 -> Expr b1 b2
stripTicksTopE p = go
  where go (Tick t e) | p t = go e
        go other            = other

stripTicksTopT :: (CoreTickish -> Bool) -> Expr b1 b2 -> [CoreTickish]
stripTicksTopT p = go []
  where go ts (Tick t e) | p t = go (t:ts) e
        go ts _                = ts

{- *********************************************************************
*                                                                      *
             Other expression construction
*                                                                      *
********************************************************************* -}

bindNonRec :: HasDebugCallStack => CoreId -> CoreExpr -> CoreExpr -> CoreExpr
bindNonRec bndr rhs body
  | Type _ <- rhs
  = panic "bindNonRec"
  | KiCo _ <- rhs
  = panic "bindNonRec"
  | Kind _ <- rhs
  = panic "bindNonRec"
  | isJoinId bndr = let_bind
  | needsCaseBinding rhs = case_bind
  | otherwise = let_bind
  where
    case_bind = panic "mkDefaultCase rhs bndr body"
    let_bind = Let (NonRec bndr rhs) body

-- TODO: this probably isn't necessarily since we have strict LET!!!
-- Probably keep it so that lets can float
needsCaseBinding :: HasDebugCallStack => CoreExpr -> Bool
needsCaseBinding rhs = not (exprOkForSpeculation rhs)

mkSingleAltCase :: CoreExpr -> CoreId -> AltCon -> [CoreId] -> CoreExpr -> CoreExpr
mkSingleAltCase scrut case_bndr con bndrs body
  = Case scrut case_bndr case_ty [Alt con bndrs body]
  where
    body_ty = exprType body

    case_ty
      | Just body_ty' <- panic "occCheckExpand bndrs body_ty"
      = body_ty'
      | otherwise
      = pprPanic "mkSingleAltCase" (ppr scrut $$ ppr bndrs $$ ppr body_ty)

{- *********************************************************************
*                                                                      *
             Operations over case alternatives
*                                                                      *
********************************************************************* -}

findAlt :: AltCon -> [Alt a b] -> Maybe (Alt a b)
findAlt con alts = case alts of
  (deflt@(Alt DEFAULT _ _) : alts) -> go alts (Just deflt)
  _ -> go alts Nothing
  where
    go [] deflt = deflt
    go (alt@(Alt con1 _ _) : alts) deflt = case con `cmpAltCon` con1 of
           LT -> deflt
           EQ -> Just alt
           GT -> assert (not (con1 == DEFAULT)) $ go alts deflt

{- *********************************************************************
*                                                                      *
             exprIsTrivial
*                                                                      *
********************************************************************* -}

{-# INLINE trivial_expr_fold #-}
trivial_expr_fold :: (CoreId -> r) -> (Literal -> r) -> r -> r -> CoreExpr -> r
trivial_expr_fold k_id k_lit k_triv k_not_triv = go
  where
    go (Var v) = k_id v
    go (Lit l) | panic "litIsTrivial l" = k_lit l
    go (Type _) = k_triv
    go (KiCo _) = k_triv
    go (Kind _) = k_triv
    go (App f t) | not (isRuntimeArg t) = go f
    go (Lam b _ e) | not (isRuntimeVar b) = go e
    go (Tick t e) | not (tickishIsCode t) = go e
    go (Cast e _) = go e
    go _ = k_not_triv

exprIsTrivial :: CoreExpr -> Bool
exprIsTrivial e = trivial_expr_fold (const True) (const True) True False e

{- *********************************************************************
*                                                                      *
             exprIsCheap, exprIsExpandable
*                                                                      *
********************************************************************* -}

type CheapAppFun = CoreId -> Arity -> Bool

{-# INLINE exprIsCheapX #-}
exprIsCheapX :: CheapAppFun -> Bool -> CoreExpr -> Bool
exprIsCheapX ok_app expandable e = ok e
  where
    ok e = go 0 e

    go n (Var v) = ok_app v n
    go _ (Lit {}) = True
    go _ (Type {}) = True
    go _ (KiCo {}) = True
    go _ (Kind {}) = True
    go n (Cast e _) = go n e
    go n (Case scrut _ _ alts) = not expandable &&
                                 ok scrut &&
                                 and [ go n rhs | Alt _ _ rhs <- alts ]
    go n (Tick t e) | tickishCounts t = False
                    | otherwise = go n e
    go n (Lam x _ e) | isRuntimeVar x = n == 0 || go (n - 1) e
                     | otherwise = go n e
    go n (App f e) | isRuntimeArg e = go (n + 1) f && ok e
                   | otherwise = go n f
    go n (Let (NonRec _ r) e) = not expandable && go n e && ok r
    go n (Let (Rec prs) e) = not expandable && go n e && all (ok . snd) prs

exprIsExpandable :: CoreExpr -> Bool
exprIsExpandable e = ok e
  where
    ok e = go 0 e

    go n (Var v) = isExpandableApp v n
    go _ (Lit {}) = True
    go _ (Type {}) = True
    go _ (KiCo {}) = True
    go _ (Kind {}) = True
    go n (Cast e _) = go n e
    go n (Tick t e) | tickishCounts t = False
                    | otherwise = go n e
    go n (Lam x k e) | isRuntimeVar x = n ==0 || go (n - 1) e
                     | otherwise = go n e
    go n (App f e) | isRuntimeArg e = go (n + 1) f && ok e
                   | otherwise = go n f
    go _ (Case {}) = False
    go _ (Let {}) = False

exprIsWorkFree :: CoreExpr -> Bool
exprIsWorkFree e = exprIsCheapX isWorkFreeApp False e

isWorkFreeApp :: CheapAppFun
isWorkFreeApp fn n_val_args
  | n_val_args == 0
  = True
  | n_val_args <- idArity fn
  = True
  | otherwise
  = case idDetails fn of
      DataConId {} -> True
      -- TODO: PrimOpId
      _ -> False

isExpandable :: CoreExpr -> Bool
isExpandable e = exprIsCheapX isExpandableApp True e

isExpandableApp :: CheapAppFun
isExpandableApp fn n_val_args
  | isWorkFreeApp fn n_val_args = True
  | otherwise
  = case idDetails fn of
      -- TODO: PrimOpId
      _ | isDeadEndId fn -> False
        | isConLikeId fn -> True
        | all_args_are_preds -> True
        | otherwise -> False
  where
    all_args_are_preds = all_pred_args n_val_args (varType fn)

    all_pred_args n_val_args ty
      | n_val_args == 0
      = True
      | Just (bndr, ty) <- splitPiTy_maybe ty
      = case bndr of
          NamedTy {} -> all_pred_args n_val_args ty
          NamedKiCo {} -> all_pred_args n_val_args ty
          NamedKi {} -> all_pred_args n_val_args ty
          AnonTy {} -> False
      | otherwise
      = False

{- *********************************************************************
*                                                                      *
             exprOkForSpeculation
*                                                                      *
********************************************************************* -}

exprOkForSpeculation :: CoreExpr -> Bool
exprOkForSpeculation = panic "unfinished"

{- *********************************************************************
*                                                                      *
             exprIsHNF, exprIsConLike
*                                                                      *
********************************************************************* -}

exprIsHNF :: CoreExpr -> Bool
exprIsHNF = exprIsHNFlike isDataConId isEvaldUnfolding

exprIsConLike :: CoreExpr -> Bool
exprIsConLike = exprIsHNFlike isConLikeId isConLikeUnfolding

exprIsHNFlike :: HasDebugCallStack => (CoreId -> Bool) -> (Unfolding -> Bool) -> CoreExpr -> Bool
exprIsHNFlike is_con is_con_unf e = is_hnf_like e
  where
    is_hnf_like (Var v) = True -- TODO (double check) our binders are always unlifted (and evald)
    -- TODO: rubbish literals if added
    is_hnf_like (Lit _) = True
    is_hnf_like (Type _) = True
    is_hnf_like (KiCo _) = True
    is_hnf_like (Kind _) = True
    is_hnf_like (Lam b _ e) = isRuntimeVar b || is_hnf_like e
    is_hnf_like (Tick tickish e) = not (tickishCounts tickish) && is_hnf_like e
    is_hnf_like (Case e _ _ _) = is_hnf_like e
    is_hnf_like (App e a)
      | isValArg a = app_is_value e [a]
      | otherwise = is_hnf_like e
    is_hnf_like (Let _ e) = panic "exprIsHNFlike" -- we DON'T have lazy let(rec), should be false like Case?
    is_hnf_like _ = False

    app_is_value :: CoreExpr -> [CoreArg] -> Bool
    app_is_value (Var f) as = id_app_is_value f as
    app_is_value (Tick _ f) as = app_is_value f as
    app_is_value (Cast f _) as = app_is_value f as
    app_is_value (App f a) as | isValArg a = app_is_value f (a:as)
                              | otherwise = app_is_value f as
    app_is_value _ _ = False

    id_app_is_value id val_args = case compare (idArity id) (length val_args) of
      EQ | is_con id -> all is_hnf_like val_args -- all fields are strict!

      -- Partial application
      GT -> all is_hnf_like val_args -- all types are unlifted

      _ -> False

exprIsTopLevelBindable :: CoreExpr -> CoreType -> Bool
exprIsTopLevelBindable expr ty = True -- TODO: check for ticked strings?

{- *********************************************************************
*                                                                      *
             CoreVarSets
*                                                                      *
********************************************************************* -}

mkCoreBndrVarSets :: [CoreBndr] -> CoreVarSets
mkCoreBndrVarSets bndrs
  = go bndrs (emptyVarSet, emptyVarSet, emptyVarSet, emptyVarSet, emptyVarSet)
  where
    go [] acc = acc
    go (Core.Id id : bndrs) (ids, tcvs, tvs, kcvs, kvs)
      = go bndrs (extendVarSet ids id, tcvs, tvs, kcvs, kvs)
    go (Tv tv : bndrs) (ids, tcvs, tvs, kcvs, kvs)
      = go bndrs (ids, tcvs, extendVarSet tvs tv, kcvs, kvs)
    go (KCv kcv : bndrs) (ids, tcvs, tvs, kcvs, kvs)
      = go bndrs (ids, tcvs, tvs, extendVarSet kcvs kcv, kvs)
    go (Kv kv : bndrs) (ids, tcvs, tvs, kcvs, kvs)
      = go bndrs (ids, tcvs, tvs, kcvs, extendVarSet kvs kv)

disjointCoreVarSets :: CoreVarSets -> CoreVarSets -> Bool
disjointCoreVarSets (ids1, tcvs1, tvs1, kcvs1, kvs1) (ids2, tcvs2, tvs2, kcvs2, kvs2)
  = disjointVarSet ids1 ids2
    && disjointVarSet tcvs1 tcvs2
    && disjointVarSet tvs1 tvs2
    && disjointVarSet kcvs1 kcvs2
    && disjointVarSet kvs1 kvs2

{- *********************************************************************
*                                                                      *
              Type utilities
*                                                                      *
********************************************************************* -}

isEmptyTy :: CoreType -> Bool
isEmptyTy ty
  | Just (tc, _) <- splitTyConApp_maybe ty
  , Just dcs <- tyConDataCons_maybe tc
  , null dcs -- TODO: must change if we add gadts
  = True
  | otherwise
  = False

{- *********************************************************************
*                                                                      *
              Join points
*                                                                      *
********************************************************************* -}

isJoinBind :: CoreBind -> Bool
isJoinBind (NonRec b _) = isJoinId b
isJoinBind (Rec ((b, _) : _)) = isJoinId b
isJoinBind _ = False

dumpIdInfoOfProgram :: Bool -> (IdInfo -> SDoc) -> CoreProgram -> SDoc
dumpIdInfoOfProgram dump_locals ppr_id_info binds = vcat (map printId ids)
  where
    ids = sortBy (stableNameCmp `on` getName) (concatMap bindersOf binds)

    printId :: CoreId -> SDoc
    printId id | isExportedId id || dump_locals = ppr id <> colon <+> ppr_id_info (idInfo id)
               | otherwise = empty
