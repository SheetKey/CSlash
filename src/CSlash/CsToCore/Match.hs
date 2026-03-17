{-# LANGUAGE LambdaCase #-}

module CSlash.CsToCore.Match where

import CSlash.Platform

import {-# SOURCE #-} CSlash.CsToCore.Expr (dsExpr)

import CSlash.Cs.Pass

import CSlash.Types.Basic

import CSlash.Types.SourceText
    ( FractionalLit,
      IntegralLit(il_value),
      negateFractionalLit,
      integralFractionalLit )
import CSlash.Driver.DynFlags
import CSlash.Cs
-- import CSlash.Cs.Syn.Type
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Utils.Monad
import CSlash.CsToCore.Pmc
import CSlash.CsToCore.Pmc.Utils
import CSlash.CsToCore.Pmc.Types ( Nablas )
import CSlash.CsToCore.Monad
import CSlash.CsToCore.Binds
import CSlash.CsToCore.GuardedRHSs
import CSlash.CsToCore.Utils
import CSlash.CsToCore.Errors.Types
-- import CSlash.CsToCore.Match.Constructor
import CSlash.CsToCore.Match.Literal

import CSlash.Core
import CSlash.Core.Utils
import CSlash.Core.Make
import CSlash.Core.ConLike
import CSlash.Core.DataCon
-- import CSlash.Core.PatSyn
import CSlash.Core.Type
import CSlash.Core.Type.Compare( eqType{-, eqTypes-} )
-- import CSlash.Core.Coercion ( eqCoercion )
-- import CSlash.Core.TyCon    ( isNewTyCon )
import CSlash.Core.Kind
import CSlash.Builtin.Types

import CSlash.Types.Var.Id
import CSlash.Types.Var.Class
import CSlash.Types.Literal
import CSlash.Types.SrcLoc

import CSlash.Data.Maybe
import CSlash.Utils.Misc
import CSlash.Types.Name hiding (varName)
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Data.FastString
import CSlash.Types.Unique
import CSlash.Types.Unique.DFM

import Control.Monad ( zipWithM, unless )
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as Map

{- *********************************************************************
*                                                                      *
                The main matching function
*                                                                      *
********************************************************************* -}

match
  :: [Id Zk]
  -> Type Zk
  -> [EquationInfo]
  -> DsM (MatchResult CoreExpr)
match [] ty eqns = assertPpr (not (null eqns)) (ppr ty) $
                   combineEqnRhss (NE.fromList eqns)
match (v:vs) ty eqns = assertPpr (all (isInternalName . varName) vars) (ppr vars) $ do
  dflags <- getDynFlags
  let platform = targetPlatform dflags
  (aux_binds, tidy_eqns) <- mapAndUnzipM (tidyEqnInfo v) eqns
  let grouped = groupEquations platform tidy_eqns
  match_results <- match_groups grouped
  return $ foldr (.) id aux_binds <$> foldr1 combineMatchResults match_results
  where
    vars = v :| vs

    dropGroup :: Functor f => f (PatGroup, EquationInfo) -> f EquationInfo
    dropGroup = fmap snd

    match_groups :: [NonEmpty (PatGroup, EquationInfoNE)] -> DsM (NonEmpty (MatchResult CoreExpr))
    match_groups [] = panic "matchEmpty v ty"
    match_groups (g:gs) = mapM match_group $ g :| gs

    match_group :: NonEmpty (PatGroup, EquationInfoNE) -> DsM (MatchResult CoreExpr)
    match_group eqns@((group, _) :| _) =
      case group of
        PgCon {} -> panic "matchConFamily vars  ty (ne $ subGroupUniq [(c, e)| (PgCon c, e) <- eqns'])"
        PgLit {} -> matchLiterals vars ty (ne $ subGroupOrd [(l, e) | (PgLit l, e) <- eqns'])
        PgN {} -> matchNPats vars ty (dropGroup eqns)
        PgOverS {} -> matchNPats vars ty (dropGroup eqns)
        PgAny -> matchVariables vars ty (dropGroup eqns)
      where
        eqns' = NE.toList eqns
        ne l = case NE.nonEmpty l of
          Just nel -> nel
          Nothing -> pprPanic "match match_group"
                     $ text "Empty result should be impossible isnce input was non-empty"

matchVariables
  :: NonEmpty (Id Zk) -> Type Zk -> NonEmpty EquationInfoNE -> DsM (MatchResult CoreExpr)
matchVariables (_ :| vars) ty eqns = match vars ty $ NE.toList $ shiftEqns eqns

{- *********************************************************************
*                                                                      *
                Tidying patterns
*                                                                      *
********************************************************************* -}

tidyEqnInfo :: Id Zk -> EquationInfo -> DsM (DsWrapper, EquationInfo)
tidyEqnInfo _ eqn@(EqnDone {}) = return (idDsWrapper, eqn)
tidyEqnInfo v eqn@(EqnMatch { eqn_pat = (L loc pat) }) = do
  (wrap, pat') <- tidy1 v (not . isGoodSrcSpan . locA $ loc) pat
  return (wrap, eqn{eqn_pat = L loc pat'})

tidy1 :: Id Zk -> Bool -> Pat Zk -> DsM (DsWrapper, Pat Zk)
tidy1 v g (ParPat _ pat) = tidy1 v g (unLoc pat)
tidy1 v g (SigPat _ pat _) = tidy1 v g (unLoc pat)
tidy1 _ _ (WildPat ty) = return (idDsWrapper, WildPat ty)
tidy1 v _ (VarPat _ (L _ var)) = return (wrapBind var v, WildPat (varType var))
tidy1 v g (AsPat _ (L _ var) pat) = do
  (wrap, pat') <- tidy1 v g (unLoc pat)
  return (wrapBind var v . wrap, pat')
tidy1 _ _ (TuplePat tys pats) = -- return (idDsWrapper, unLoc tuple_ConPat)
  pprPanic "what about the ki and kicos?"
  $ vcat [ ppr tys, ppr pats ]
  -- where
  --   arity = length pats
  --   tuple_ConPat = mkPrefixConPat (tupleDataCon arity) pats tys
tidy1 _ _ (SumPat tys pat alt arity) = -- return (idDsWrapper, unLoc sum_ConPat)
  pprPanic "what about the kis and kicos?"
  $ vcat [ ppr tys, ppr pat, ppr alt, ppr arity ]
  -- where
  --   sum_ConPat = mkPrefixConPat (sumDataCon alt arity) [pat] tys
tidy1 _ g (LitPat _ lit) = do
  unless g $ warnAboutOverflowedLit lit
  return (idDsWrapper, tidyLitPat lit)
-- tidy1 _ _ (OrPat ty lpats) = panic "not implemented" TODO
tidy1 _ _ non_interesting_pat = return (idDsWrapper, non_interesting_pat)

{- *********************************************************************
*                                                                      *
                matchWrapper
*                                                                      *
********************************************************************* -}

matchWrapper
  :: CsMatchContextRn
  -> Maybe [LCsExpr Zk]
  -> MatchGroup Zk (LCsExpr Zk)
  -> DsM ([Id Zk], CoreExpr)
matchWrapper ctxt scrs (MG { mg_alts = L _ matches
                             , mg_ext = MatchGroup arg_tys rhs_ty origin })
  = do dflags <- getDynFlags
       locn <- getSrcSpanDs
       new_vars <- case matches of
                     [] -> newSysLocalsDs arg_tys
                     (m:_) -> assert (arg_tys `equalLength` (csLMatchPats m)) $
                              selectMatchVars (unLoc <$> csLMatchPats m)
       tracePm "matchWrapper"
         $ vcat [ ppr ctxt
                , text "scrs" <+> ppr scrs
                , text "matches group" <+> ppr matches
                , text "matchPmChecked" <+> ppr (isMatchContextPmChecked dflags origin ctxt) ]
       matches_nablas <-
         if isMatchContextPmChecked dflags origin ctxt
         then addCsScrutTmCs (concat scrs) new_vars $
              pmcMatches origin (DsMatchContext ctxt locn) new_vars matches
         else panic "not implemented"

       eqns_info <- zipWithM mk_eqn_info matches matches_nablas

       result_expr <- discard_warnings_if_skip_pmc origin $
                      matchEquations ctxt new_vars eqns_info rhs_ty

       return (new_vars, result_expr)
  where
    mk_eqn_info :: LMatch Zk (LCsExpr Zk) -> (Nablas, NonEmpty Nablas) -> DsM EquationInfo
    mk_eqn_info (L _ (Match { m_pats = L _ pats, m_grhss = grhss })) (pat_nablas, rhss_nablas)
      = do dflags <- getDynFlags
           let upats = pats-- TODO: decideBangHood: how did I deal with this elsewhere
           match_result <- updPmNablas pat_nablas $
                           dsGRHSs ctxt grhss rhs_ty rhss_nablas
           return $ mkEqnInfo upats match_result

    discard_warnings_if_skip_pmc orig = panic "I may not want to discard these"
    
matchEquations
  :: CsMatchContextRn
  -> [Id Zk]
  -> [EquationInfo]
  -> Type Zk
  -> DsM CoreExpr
matchEquations ctxt vars eqns_info rhs_ty = do
  match_result <- match vars rhs_ty eqns_info
  fail_expr <- mkFailExpr ctxt rhs_ty
  extractMatchResult match_result fail_expr

matchSinglePatVar
  :: Id Zk
  -> Maybe CoreExpr
  -> CsMatchContextRn
  -> LPat Zk
  -> Type Zk
  -> MatchResult CoreExpr
  -> DsM (MatchResult CoreExpr)
matchSinglePatVar var mb_scrut ctx pat ty match_result
  = assertPpr (isInternalName (varName var)) (ppr var) $ do
      dflags <- getDynFlags
      locn <- getSrcSpanDs
      ldi_nablas <- if isMatchContextPmChecked_SinglePat dflags FromSource ctx pat
        then addCoreScrutTmCs (maybeToList mb_scrut) [var] $
             pmcPatBind (DsMatchContext ctx locn) var (unLoc pat)
        else getLdiNablas

      let eqn_info = EqnMatch { eqn_pat = pat -- TODO: decideBangHood
                              , eqn_rest = EqnDone $
                                updPmNablasMatchResult ldi_nablas match_result }
      match [var] ty [eqn_info]

updPmNablasMatchResult :: Nablas -> MatchResult r -> MatchResult r
updPmNablasMatchResult nablas = \case
  MR_Infallible body_fn -> MR_Infallible $ updPmNablas nablas body_fn
  MR_Fallible body_fn -> MR_Fallible $ \fail -> updPmNablas nablas $ body_fn fail

{- *********************************************************************
*                                                                      *
                Pattern classification
*                                                                      *
********************************************************************* -}

data PatGroup
  = PgAny
  | PgCon (DataCon Zk)
  | PgLit Literal
  | PgN FractionalLit
  | PgOverS FastString

instance Show PatGroup where
  show PgAny = "PgAny"
  show (PgCon _) = "PgCon"
  show (PgLit _) = "PgLit"
  show _ = "PgOther"

groupEquations :: Platform -> [EquationInfoNE] -> [NonEmpty (PatGroup, EquationInfoNE)]
groupEquations platform eqns
  = NE.groupBy same_gp $ [(patGroup platform (firstPat eqn), eqn) | eqn <- eqns]
  where
    same_gp (pg1, _) (pg2, _) = pg1 `sameGroup` pg2

subGroup
  :: (m -> [NonEmpty EquationInfo])
  -> m
  -> (a -> m -> Maybe (NonEmpty EquationInfo))
  -> (a -> NonEmpty EquationInfo -> m -> m)
  -> [(a, EquationInfo)] -> [NonEmpty EquationInfo]
subGroup elems empty lookup insert group
  = fmap NE.reverse $ elems $ foldl' accumulate empty group
  where
    accumulate pg_map (pg, eqn) =
      case lookup pg pg_map of
        Just eqns -> insert pg (NE.cons eqn eqns) pg_map
        Nothing -> insert pg (NE.fromList [eqn]) pg_map

subGroupOrd :: Ord a => [(a, EquationInfo)] -> [NonEmpty EquationInfo]
subGroupOrd = subGroup Map.elems Map.empty Map.lookup Map.insert

subGroupUniq :: Uniquable a => [(a, EquationInfo)] -> [NonEmpty EquationInfo]
subGroupUniq = subGroup eltsUDFM emptyUDFM (flip lookupUDFM) (\k v m -> addToUDFM m k v)

sameGroup :: PatGroup -> PatGroup -> Bool
sameGroup PgAny PgAny = True
sameGroup (PgCon _) (PgCon _) = True
sameGroup (PgLit _) (PgLit _) = True
sameGroup (PgN l1) (PgN l2) = l1 == l2
sameGroup (PgOverS s1) (PgOverS s2) = s1 == s2
sameGroup _ _ = False

patGroup :: Platform -> Pat Zk -> PatGroup
patGroup _ (ConPat { pat_con = L _ con, pat_con_ext = ConPatTc }) = panic "unfinished"
patGroup _ (WildPat {}) = PgAny
patGroup _ (NPat _ (L _ OverLit { ol_val = oval }) mb_neg _) =
  case (oval, isJust mb_neg) of
    (CsIntegral i, is_neg) -> PgN (integralFractionalLit is_neg (if is_neg
                                                                 then negate (il_value i)
                                                                 else il_value i))
    _--(CsFractional f, is_neg)
      -> panic "unfinished"
patGroup _ pat = pprPanic "patGroup" (ppr pat)
