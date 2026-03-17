{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.CsToCore.Pmc.Solver where

import CSlash.Cs.Pass

import CSlash.CsToCore.Pmc.Types
import CSlash.CsToCore.Pmc.Utils (tracePm, traceWhenFailPm, mkPmId)
import CSlash.CsToCore.Types (DsGblEnv(..))

import CSlash.Driver.DynFlags
import CSlash.Driver.Config
import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Monad (allM)
import CSlash.Utils.Panic
import CSlash.Data.Bag

import CSlash.Types.CompleteMatch
import CSlash.Types.Unique.Set
import CSlash.Types.Unique.DSet
import CSlash.Types.Unique.SDFM
import CSlash.Types.Var.Id
import CSlash.Types.Var.Class
import CSlash.Types.Name
import CSlash.Types.Name.Reader (lookupGRE_Name, GlobalRdrEnv)
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Unique.Supply

import CSlash.Tc.Utils.Monad   (getGblEnv)

import CSlash.Core
import CSlash.Core.FVs         (exprFreeVars)
import CSlash.Core.Type.Compare( eqType )
import CSlash.Core.Map.Expr
-- import CSlash.Core.Predicate (typeDeterminesValue, mkNomEqPred)
import CSlash.Core.SimpleOpt (simpleOptExpr, exprIsConApp_maybe)
import CSlash.Core.Utils     (exprType)
-- import CSlash.Core.Make      (mkListExpr, mkCharExpr, mkImpossibleExpr)
import CSlash.Core.Subst

import CSlash.Data.FastString
import CSlash.Types.SrcLoc
import CSlash.Data.Maybe
import CSlash.Core.ConLike
import CSlash.Core.DataCon
-- import CSlash.Core.PatSyn
import CSlash.Core.TyCon
-- import CSlash.Core.TyCon.RecWalk
import CSlash.Builtin.Names
import CSlash.Builtin.Types
import CSlash.Core.Type.Rep
-- import CSlash.Core.Subst (elemSubst)
import CSlash.Core.Type
-- import CSlash.Tc.Solver   (tcNormalise, tcCheckGivens, tcCheckWanteds)
-- import CSlash.Core.Unify    (tcMatchTy)
-- import CSlash.Core.Coercion
import CSlash.Core.Reduction
import CSlash.CsToCore.Monad hiding (foldlM)

import Control.Applicative ((<|>))
import Control.Monad (foldM, forM, guard, mzero, when, filterM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict
import Data.Coerce
import Data.Foldable (foldlM, toList)
import Data.Monoid   (Any(..))
import Data.List     (sortBy, find)
import qualified Data.List.NonEmpty as NE
import Data.Ord      (comparing)

addPhiCtsNablas :: Nablas -> PhiCts -> DsM Nablas
addPhiCtsNablas nablas cts = liftNablasM (\d -> addPhiCts d cts) nablas

addPhiCtNablas :: Nablas -> PhiCt -> DsM Nablas
addPhiCtNablas nablas ct = addPhiCtsNablas nablas (unitBag ct)

liftNablasM :: Monad m => (Nabla -> m (Maybe Nabla)) -> Nablas -> m Nablas
liftNablasM f (MkNablas ds) = MkNablas . catBagMaybes <$> (traverse f ds)

isInhabited :: Nablas -> DsM Bool
isInhabited (MkNablas ds) = pure (not (null ds))

vanillaCompleteMatchTC :: TyCon Zk -> Maybe DsCompleteMatch
vanillaCompleteMatchTC tc =
  let mb_dcs = tyConDataCons_maybe tc
  in vanillaCompleteMatch . mkUniqDSet . map RealDataCon <$> mb_dcs
 
addTyConMatches :: TyCon Zk -> ResidualCompleteMatches -> DsM ResidualCompleteMatches
addTyConMatches tc rcm = pure $ add_tc_match rcm
  where
    add_tc_match rcm = rcm { rcm_vanilla = rcm_vanilla rcm <|> vanillaCompleteMatchTC tc }

data PhiCt
  = PhiTyCt !(PredType Zk)
  | PhiCoreCt !(Id Zk) !CoreExpr
  | PhiConCt !(Id Zk) !PmAltCon ![TyVar Zk] ![Id Zk]
  | PhiNotConCt !(Id Zk) !PmAltCon
  | PhiBotCt !(Id Zk) -- probably remove this field
  | PhiNotBotCt !(Id Zk)

instance Outputable PhiCt where
  ppr (PhiTyCt ty_ct) = ppr ty_ct
  ppr (PhiCoreCt x e) = ppr x <+> char '~' <+> ppr e
  ppr (PhiConCt x con tvs args)
    = hsep (ppr con : pp_tvs ++ pp_args) <+> text "<-" <+> ppr x
    where
      pp_tvs = map (braces . ppr) tvs
      pp_args = map ppr args
  ppr (PhiNotConCt x con) = ppr x <+> text "≁" <+> ppr con
  ppr (PhiBotCt x) = ppr x <+> text "~ ⊥"
  ppr (PhiNotBotCt x) = ppr x <+> text "≁ ⊥"

type PhiCts = Bag PhiCt

initFuel :: Int
initFuel = 4

addPhiCts :: Nabla -> PhiCts -> DsM (Maybe Nabla)
addPhiCts nabla cts = runMaybeT $ do
  let (ty_cts, tm_cts) = partitionPhiCts cts
  nabla' <- addTyCts nabla (listToBag ty_cts)
  nabla'' <- foldlM addPhiTmCt nabla' (listToBag tm_cts)
  inhabitationTest initFuel (nabla_ty_st nabla) nabla''

partitionPhiCts :: PhiCts -> ([PredType Zk], [PhiCt])
partitionPhiCts = partitionWith to_either . toList
  where
    to_either (PhiTyCt pred_ty) = Left pred_ty
    to_either ct = Right ct

addTyCts :: Nabla -> Bag (PredType Zk) ->MaybeT DsM Nabla
addTyCts nabla@(MkNabla { nabla_ty_st = ty_st }) new_ty_cs = do
  ty_st' <- MaybeT (tyOracle ty_st new_ty_cs)
  pure nabla { nabla_ty_st = ty_st' }

tyOracle :: TyState -> Bag (PredType Zk) -> DsM (Maybe TyState)
tyOracle ty_st@(TySt n inert) cts
  | isEmptyBag cts
  = pure (Just ty_st)
  | otherwise
  = {-# SCC "tyOracle" #-}
    do cvs <- traverse nameTyCt cts
       tracePm "tyOracle" (ppr n $$ ppr cts $$ ppr inert)
       mb_new_inert <- initTcDsForSolver $ panic "tcCheckGivens inert cvs"
       return (TySt (n+1) <$> mb_new_inert)

nameTyCt :: PredType Zk -> DsM (TyCoVar Zk)
nameTyCt pred_ty = do
  unique <- getUniqueM
  let occName = mkVarOccFS (fsLit ("pm_" ++ show unique))
  return $ panic "mkTyCoVar occName unique pred_ty noSrcSpan"

addPhiTmCt :: Nabla -> PhiCt -> MaybeT DsM Nabla
addPhiTmCt _ (PhiTyCt ct) = pprPanic "addPhiCt:TyCt" (ppr ct)
addPhiTmCt nabla (PhiCoreCt x e) = addCoreCt nabla x e
addPhiTmCt nabla (PhiConCt x con tvs args) = do
  nabla' <- addConCt nabla x con tvs args
  foldlM addNotBotCt nabla' args -- all args are strict
addPhiTmCt nabla (PhiNotConCt x con) = addNotConCt nabla x con
addPhiTmCt nabla (PhiBotCt x) = addBotCt nabla x
addPhiTmCt nabla (PhiNotBotCt x) = addNotBotCt nabla x

addBotCt :: Nabla -> Id Zk -> MaybeT DsM Nabla
addBotCt nabla@MkNabla{ nabla_tm_st = ts } x = do
  let vi@VI{ vi_bot = bot } = lookupVarInfo ts x
  case bot of
    IsNotBot -> mzero
    IsBot -> pure nabla
    MaybeBot -> mzero -- all types are unlifted    

addNotBotCt :: Nabla -> Id Zk -> MaybeT DsM Nabla
addNotBotCt nabla@MkNabla{ nabla_tm_st = ts@TmSt{ ts_facts = env } } x = do
  let vi@VI { vi_bot = bot } = lookupVarInfo ts x
  case bot of
    IsBot -> mzero
    IsNotBot -> pure nabla
    MaybeBot -> do
      let vi' = vi { vi_bot = IsNotBot }
      pure $ markDirty x
           $ nabla { nabla_tm_st = ts { ts_facts = addToUSDFM env x vi' } }

addNotConCt :: Nabla -> Id Zk -> PmAltCon -> MaybeT DsM Nabla
addNotConCt nabla x nalt = do
  (mb_mark_dirty, nabla') <- tryVarInfo go nabla x
  pure $ case mb_mark_dirty of
    Just x -> markDirty x nabla'
    Nothing -> nabla'
  where
    go :: VarInfo -> MaybeT DsM (Maybe (Id Zk), VarInfo)
    go vi@(VI x' pos neg _ rcm) = do
      let contradicts nalt sol = eqPmAltCon (paca_con sol) nalt == Equal
      guard (not (any (contradicts nalt) pos))

      let implies nalt sol = eqPmAltCon (paca_con sol) nalt == Disjoint
      let neg' | any (implies nalt) pos = neg
               | hasRequiredTheta nalt = neg -- TODO: for patsyns
               | otherwise = panic "extendPmAltConSet neg nalt"
      let vi' = vi { vi_neg = neg', vi_bot = IsNotBot }
      mb_rcm' <- lift (panic "markMatched nalt rcm")
      pure $ case mb_rcm' of
        Just rcm' -> (Just x', vi' { vi_rcm = rcm' })
        Nothing -> (Nothing, vi')

hasRequiredTheta :: PmAltCon -> Bool
hasRequiredTheta (PmAltConLike (RealDataCon{})) = False -- True for some patsyns
hasRequiredTheta _ = False

addConCt :: Nabla -> Id Zk -> PmAltCon -> [TyVar Zk] -> [Id Zk] -> MaybeT DsM Nabla
addConCt nabla@MkNabla{ nabla_tm_st = ts@TmSt{ ts_facts = env } } x alt tvs args = do
  let vi@(VI _ pos neg bot _) = lookupVarInfo ts x
  guard (not (panic "elemPmAltConSet alt neg"))
  guard (all ((/= Disjoint) . eqPmAltCon alt . paca_con) pos)
  case find ((== Equal) . eqPmAltCon alt . paca_con) pos of
    Just (PACA _ other_tvs other_args) -> do
      let ty_cts = equateTys (map mkTyVarTy tvs) (map mkTyVarTy other_tvs)
      nabla' <- MaybeT $ addPhiCts nabla (listToBag ty_cts)
      let add_var_ct nabla (a, b) = addVarCt nabla a b
      foldlM add_var_ct nabla' $ zipEqual "addConCt" args other_args
    Nothing -> do
      let pos' = PACA alt tvs args : pos
      let nabla_with bot' = nabla { nabla_tm_st = ts { ts_facts =
                                                       addToUSDFM env x (vi { vi_pos = pos'
                                                                            , vi_bot = bot' })}}
      pure (nabla_with IsNotBot)

equateTys :: [Type Zk] -> [Type Zk] -> [PhiCt]
equateTys ts us = [ PhiTyCt (mkTyEqPred t u)
                  | (t, u) <- zipEqual "equateTys" ts us
                  , not (eqType t u) ]

addVarCt :: Nabla -> Id Zk -> Id Zk -> MaybeT DsM Nabla
addVarCt nabla@MkNabla{ nabla_tm_st = ts@TmSt{ ts_facts = env } } x y =
  case equateUSDFM env x y of
    (Nothing, env') -> pure $ nabla { nabla_tm_st = ts { ts_facts = env' } }
    (Just vi_x, env') -> do
      let nabla_equated = nabla { nabla_tm_st = ts { ts_facts = env' } }
      let add_pos nabla (PACA cl tvs args) = addConCt nabla y cl tvs args
      nabla_pos <- foldlM add_pos nabla_equated (vi_pos vi_x)
      let add_neg nabla nalt = addNotConCt nabla y nalt
      foldlM add_neg nabla_pos (pmAltConSetElems (vi_neg vi_x))

addCoreCt :: Nabla -> Id Zk -> CoreExpr -> MaybeT DsM Nabla
addCoreCt nabla x e = do
  simpl_opts <- initSimpleOpts <$> getDynFlags
  let e' = simpleOptExpr simpl_opts e
  execStateT (core_expr x e') nabla
  where
    core_expr :: Id Zk -> CoreExpr -> StateT Nabla (MaybeT DsM) ()
    core_expr x (Cast e _) = core_expr x e
    core_expr x (Tick _ e) = core_expr x e
    core_expr x e
      | Just lit <- panic "coreExprAsPmLit e"
      = panic "pm_lit x lit"
      | Just (in_scope, [], dc, _, args) <- exprIsConApp_maybe in_scope_env e
      = data_con_app x in_scope dc args
      | Var y <- e, Nothing <- isDataConId_maybe x
      = modifyT (\nabla -> addVarCt nabla x y)
      | otherwise
      = equate_with_similar_expr x e
      where
        expr_in_scope = mkTermInScopeSets (exprFreeVars e)
        in_scope_env = ISE expr_in_scope noUnfoldingFun

    equate_with_similar_expr :: Id Zk -> CoreExpr -> StateT Nabla (MaybeT DsM) ()
    equate_with_similar_expr x e = do
      rep <- StateT $ \nabla -> lift (representCoreExpr nabla e)
      modifyT (\nabla -> addVarCt nabla x rep)

    bind_expr :: CoreExpr -> StateT Nabla (MaybeT DsM) (Id Zk)
    bind_expr e = do
      x <- lift (lift (mkPmId (exprType e)))
      core_expr x e
      pure x

    data_con_app
      :: Id Zk
      -> TermSubstInScope
      -> DataCon Zk
      -> [CoreExpr]
      -> StateT Nabla (MaybeT DsM) ()
    data_con_app x in_scope dc args = do -- TODO: deal with existentials
      let arity = panic "dataConSourceArity dc"
          vis_args = reverse $ take arity $ reverse args
      uniq_supply <- lift $ lift $ getUniqueSupplyM
      modifyT $ \nabla -> addNotBotCt nabla x
      arg_ids <- traverse bind_expr vis_args
      pm_alt_con_app x (PmAltConLike (RealDataCon dc)) arg_ids

    pm_lit :: Id Zk -> PmLit -> StateT Nabla (MaybeT DsM) ()
    pm_lit x lit = do
      modifyT $ \nabla -> addNotBotCt nabla x
      pm_alt_con_app x (PmAltLit lit) []

    pm_alt_con_app :: Id Zk -> PmAltCon -> [Id Zk] -> StateT Nabla (MaybeT DsM) ()
    pm_alt_con_app x con args = modifyT $ \nabla -> addConCt nabla x con [] args

modifyT :: Monad m => (s -> m s) -> StateT s m ()
modifyT f = StateT $ fmap ((,) ()) . f

representCoreExpr :: Nabla -> CoreExpr -> DsM (Id Zk, Nabla)
representCoreExpr nabla@MkNabla{ nabla_tm_st = ts@TmSt{ ts_reps = reps } } e
  | Just res <- panic "lookupCoreMap reps e"
  = pure (res, nabla)
  | otherwise
  = do rep <- mkPmId (exprType e)
       let reps' = panic "extendCoreMap reps e rep"
       let nabla' = nabla { nabla_tm_st = ts { ts_reps = reps' } }
       pure (rep, nabla')

tyStateRefined :: TyState -> TyState -> Bool
tyStateRefined a b = ty_st_n a /= ty_st_n b

markDirty :: Id Zk -> Nabla -> Nabla
markDirty x nabla@MkNabla{ nabla_tm_st = ts@TmSt{ ts_dirty = dirty } }
  = nabla { nabla_tm_st = ts { ts_dirty = extendDVarSet dirty x } }

traverseDirty :: Monad m => (VarInfo -> m VarInfo) -> TmState -> m TmState
traverseDirty f ts@TmSt{ ts_facts = env, ts_dirty = dirty }
  = go (uniqDSetToList dirty) env
  where
    go [] env = pure ts{ ts_facts = env }
    go (x:xs) !env = do
      vi' <- f (lookupVarInfo ts x)
      go xs (addToUSDFM env x vi')

traverseAll :: Monad m => (VarInfo -> m VarInfo) -> TmState -> m TmState
traverseAll f ts@TmSt{ ts_facts = env } = do
  env' <- traverseUSDFM f env
  pure ts { ts_facts = env' }

inhabitationTest :: Int -> TyState -> Nabla -> MaybeT DsM Nabla
inhabitationTest 0 _ nabla = pure nabla
inhabitationTest fuel old_ty_st nabla@MkNabla{ nabla_tm_st = ts } = {-# SCC "inhabitationTest" #-} do
  ts' <- if tyStateRefined old_ty_st (nabla_ty_st nabla)
         then traverseAll test_one ts
         else traverseDirty test_one ts
  pure nabla { nabla_tm_st = ts' { ts_dirty = emptyDVarSet } }
  where
    nabla_not_dirty = nabla { nabla_tm_st = ts { ts_dirty = emptyDVarSet } }
    test_one vi = lift (varNeedsTesting old_ty_st nabla vi) >>= \case
      True -> instantiate (fuel - 1) nabla_not_dirty vi
      _ -> pure vi

varNeedsTesting :: TyState -> Nabla -> VarInfo -> DsM Bool
varNeedsTesting _ MkNabla{ nabla_tm_st = tm_st } vi
  | elemDVarSet (vi_id vi) (ts_dirty tm_st) = pure True
varNeedsTesting _ _ vi
  | notNull (vi_pos vi) = pure False
varNeedsTesting old_ty_st MkNabla{ nabla_ty_st = new_ty_st } _
  | not (tyStateRefined old_ty_st new_ty_st) = pure False
varNeedsTesting old_ty_st MkNabla{ nabla_ty_st = new_ty_st } vi = do
  panic "varNeedsTesting" -- we don't have type normalization so this should be pretty simple

instantiate :: Int -> Nabla -> VarInfo -> MaybeT DsM VarInfo
instantiate fuel nabla vi = {-# SCC "instantiate" #-}
  (instBot fuel nabla vi <|> instCompleteSets fuel nabla vi)

instBot :: Int -> Nabla -> VarInfo -> MaybeT DsM VarInfo
instBot _ nabla vi = {-# SCC "instBot" #-} do
  _ <- addBotCt nabla (vi_id vi)
  pure vi

addNormalizedTypeMatches :: Nabla -> Id Zk -> DsM (ResidualCompleteMatches, Nabla)
addNormalizedTypeMatches nabla@MkNabla{ nabla_ty_st = ty_st } x
  = tryVarInfo add_matches nabla x
  where
    add_matches vi@VI{ vi_rcm = rcm }
      | isRcmInitialized rcm = pure (rcm, vi)
    add_matches vi@VI{ vi_rcm = rcm } = do
      let norm_res_ty = varType x
      rcm' <- case splitTyConApp_maybe norm_res_ty of
                Just (tc, _) -> addTyConMatches tc rcm
                Nothing -> pure rcm
      pure (rcm', vi { vi_rcm = rcm' })

instCompleteSets :: Int -> Nabla -> VarInfo -> MaybeT DsM VarInfo
instCompleteSets fuel nabla vi = {-# SCC "instCompleteSets" #-} do
  let x = vi_id vi
  (rcm, nabla) <- lift (addNormalizedTypeMatches nabla x)
  nabla <- foldlM (\nabla cls -> instCompleteSet fuel nabla x cls) nabla (getRcm rcm)
  pure (lookupVarInfo (nabla_tm_st nabla) x)

anyConLikeSolution :: (ConLike Zk -> Bool) -> [PmAltConApp] -> Bool
anyConLikeSolution p = any (go . paca_con)
  where
    go (PmAltConLike cl) = p cl
    go _ = False

instCompleteSet :: Int -> Nabla -> Id Zk -> DsCompleteMatch -> MaybeT DsM Nabla
instCompleteSet fuel nabla x cs
  | anyConLikeSolution (`elementOfUniqDSet` (cmConLikes cs)) (vi_pos vi)
  = pure nabla
  | not (completeMatchAppliesAtType (varType x) cs)
  = pure nabla
  | otherwise
  = {-# SCC "instCompleteSet" #-} go nabla (sorted_candidates cs)
  where
    vi = lookupVarInfo (nabla_tm_st nabla) x

    sorted_candidates :: DsCompleteMatch -> [ConLike Zk]
    sorted_candidates cm
      | sizeUniqDSet cs <= 5 = sortBy compareConLikeTestability (uniqDSetToList cs)
      | otherwise = uniqDSetToList cs
      where cs = cmConLikes cm
        
    go :: Nabla -> [ConLike Zk] -> MaybeT DsM Nabla  
    go _ [] = mzero
    go nabla (RealDataCon dc : _)
      | isDataConTriviallyInhabited dc
      = pure nabla
    go nabla (con:cons) = do
      let x = vi_id vi
      let recur_not_con = do
            nabla' <- addNotConCt nabla x (PmAltConLike con)
            go nabla' cons
      (nabla <$ instCon fuel nabla x con)
        <|> recur_not_con

isDataConTriviallyInhabited :: DataCon Zk -> Bool
isDataConTriviallyInhabited dc = isTyConTriviallyInhabited (dataConTyCon dc) 

isTyConTriviallyInhabited :: TyCon Zk -> Bool
isTyConTriviallyInhabited tc = memberUniqueSet (getUnique tc) triviallyInhabitedTyConKeys

triviallyInhabitedTyConKeys :: UniqueSet
triviallyInhabitedTyConKeys = fromListUniqueSet
  [ panic "need to fill" ]

compareConLikeTestability :: ConLike Zk -> ConLike Zk -> Ordering
compareConLikeTestability PatSynCon _ = GT
compareConLikeTestability _ PatSynCon = GT
compareConLikeTestability (RealDataCon a) (RealDataCon b)
  = panic "compareconliketestability"

instCon :: Int -> Nabla -> Id Zk -> ConLike Zk -> MaybeT DsM Nabla
instCon = panic "instCon"
-- instCon fuel nabla@MkNabla{ nabla_ty_st = ty_st } x con = {-# SCC "instCon" #-} MaybeT $ do
--   let hdr what = "instCon " ++ show fuel ++ " " ++ what
--   let match_ty = varType x
--   tracePm (hdr "{") $ ppr con <+> text "... <-" <+> ppr x <+> colon <+> ppr match_ty
--   let norm_match_ty = match_ty
--   mb_sigma_univ <- matchConLikeResTy ty_st norm_match_ty con
--   case mb_sigma_univ of
--     Just sigma_univ -> do
--       let (_univ_kvs, ex_kcvs, _univ_tvs, field_tys, _con_res_ty) = conLikeFullSig con

--       (sigma_ex_kcv, _) <- cloneKiCoVarBndrs sigma_univ ex_kcvs <$> getUniqueSupplyM

--       let field_tys' = substTys sigma_ex_kcv field_tys
--       arg_ids <- mapM mkPmId field_tys'

--       tracePm (hdr "(cts)")
--         $ vcat [ ppr x <+> colon <+> ppr match_ty
--                , text "In WHNF:" <+> ppr (isSourceTypeInWHNF match_ty) <+> ppr norm_match_ty
--                , ppr con <+> colon <+> text "... ->" <+> ppr _con_res_ty
--                , ppr (map (\kv -> ppr kv <+> text ":->" <+> (substKiVar sigma_univ kv))
--                       _univ_kvs)
--                , ppr (map (\tv -> ppr tv <+> text ":->" <+> (substTyVar sigma_univ tv))
--                       _univ_tvs)
--                , ppr (map (\x -> ppr x <+> colon <+> ppr (varType x)) arg_ids)
--                ]
--       runMaybeT $ do
--         let alt = PmAltConLike con
--         let branching_factor = length arg_ids
--         let ct = PhiConCt x alt [] arg_ids
--         nabla1 <- traceWhenFailPm (hdr "(ct unsatisfiable) }") (ppr ct) $
--                   addPhiTmCt nabla ct

--         let new_fuel | branching_factor <= 1 = fuel
--                      | otherwise = min fuel 2
--         lift 4 tracePm (hdr "(ct satisfiable)")
--           $ vcat [ ppr ct
--                  , ppr x <+> colon <+> ppr match_ty
--                  , text "InWHNF:" <+> ppr (isSourceTypeInWHNF match_ty) <+> ppr norm_match_ty
--                  , ppr con <+> colon <+> text "... ->" <+> ppr _con_res_ty
--                  , ppr (map (\kv -> ppr kv <+> text ":->" <+> (substKiVar sigma_univ kv))
--                         _univ_kvs)
--                  , ppr (map (\tv -> ppr tv <+> text ":->" <+> (substTyVar sigma_univ tv))
--                         _univ_tvs)
--                  , ppr (map (\x -> ppr x <+> colon <+> ppr (varType x)) arg_ids)
--                  , ppr branching_fuel
--                  , ppr new_fuel
--                  ]

--         nabla2 <- traceWhenFailPm (hdr "(inh test failed) }") (ppr nabla1) $
--                   inhabitationTest new_fuel (nablat_ty_st nabla) nabla1
--         lift $ tracePm (hdr "(inh test succeeded) }") (ppr nabla2)
--         pure nabla2

--     Nothing -> do
--       tracePm (hdr "(match_ty not instance of res_ty) }") empty
--       pure $ Just nabla
        
matchConLikeResTy :: TyState -> Type Zk -> ConLike Zk -> DsM (Maybe CoreSubst)
matchConLikeResTy _ ty (RealDataCon dc) = pure $ do
  (tc, tc_args) <- splitTyConApp_maybe ty
  if tc == dataConTyCon dc
    then panic "Just (zipSubst (dataConUnivVars dc) tc_args)"
    else Nothing
matchConLikeResTy _ _ PatSynCon = panic "unfinished"
