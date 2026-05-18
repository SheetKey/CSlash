{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Opt.Arity where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Core as Core
import CSlash.Core.Make
import CSlash.Core.FVs
import CSlash.Core.Type.FVs
import CSlash.Core.Utils
import CSlash.Core.DataCon
import CSlash.Core.TyCon     ( TyCon, tyConArity, isInjectiveTyCon )
-- import CSlash.Core.TyCon.RecWalk     ( initRecTc, checkRecTc )

import CSlash.Core.Subst
import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Core.Type.Compare( eqType )

import CSlash.Types.Demand
-- import CSlash.Types.Cpr( CprSig, mkCprSig, botCpr )
import CSlash.Types.Var.Id
import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Basic
import CSlash.Types.Tickish

import CSlash.Builtin.Types.Prim
import CSlash.Builtin.Uniques

import CSlash.Data.FastString
import CSlash.Data.Graph.UnVar
import CSlash.Data.Pair

import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc
import CSlash.Utils.Trace

import Data.List.NonEmpty ( nonEmpty )
import qualified Data.List.NonEmpty as NE
import Data.Maybe( isJust )

manifestArity :: CoreExpr -> Arity
manifestArity (Lam v _ e) | isRuntimeVar v = 1 + manifestArity e
                          | otherwise = manifestArity e
manifestArity (Tick t e) | not (tickishIsCode t) = manifestArity e
manifestArity (Cast e _) = manifestArity e
manifestArity _ = 0

joinRhsArity :: CoreExpr -> JoinArity
joinRhsArity (Lam _ _ e) = 1 + joinRhsArity e
joinRhsArity _ = 0

exprBotStrictness_maybe :: CoreExpr -> Maybe (Arity, DmdSig)
exprBotStrictness_maybe e = arityTypeBotSigs_maybe (cheapArityType e)

arityTypeBotSigs_maybe :: ArityType -> Maybe (Arity, DmdSig)
arityTypeBotSigs_maybe (AT lams div)
  | isDeadEndDiv div = Just (arity, mkVanillaDmdSig arity botDiv)
  | otherwise = Nothing
  where
    arity = length lams

{- *********************************************************************
*                                                                      *
              typeArity
*                                                                      *
********************************************************************* -}

typeArity :: CoreType -> Arity
typeArity = length . typeOneShots

typeOneShots :: CoreType -> [OneShotInfo]
typeOneShots ty = go ty
  where
    go ty
      | (_:_, ty') <- splitBigLamTyBinders ty
      = go ty'
      | (_:_, ty') <- splitForAllKiCoVars ty
      = go ty'
      | (_:_, ty') <- splitForAllForAllTyBinders ty
      = go ty'
      | Just (_, _, res) <- splitFunTy_maybe ty
      = NoOneShotInfo : go res
      | otherwise
      = []
      
isOneShotBndr :: CoreBndr -> Bool
isOneShotBndr Tv{} = True
isOneShotBndr KCv{} = True -- TODO: double check
isOneShotBndr Kv{} = True
isOneShotBndr (Core.Id id) = idOneShotInfo id == OneShotLam

{- *********************************************************************
*                                                                      *
           Computing the "arity" of an expression
*                                                                      *
********************************************************************* -}

data ArityType = AT ![ATLamInfo] !Divergence
  deriving Eq

type ATLamInfo = (Cost, OneShotInfo)

type SafeArityType = ArityType

data Cost = IsCheap | IsExpensive
  deriving Eq

allCosts :: (a -> Cost) -> [a] -> Cost
allCosts f xs = foldr (addCost . f) IsCheap xs

addCost :: Cost -> Cost -> Cost
addCost IsCheap IsCheap = IsCheap
addCost _ _ = IsExpensive

instance Outputable ArityType where
  ppr (AT oss div)
    | null oss = pp_div div
    | otherwise = char '\\' <> hcat (map pp_os oss) <> dot <> pp_div div
    where
      pp_div Diverges = char '⊥'
      pp_div ExnOrDiv = char 'x'
      pp_div Dunno    = char 'T'
      pp_os (IsCheap, OneShotLam) = text "(C1)"
      pp_os (IsExpensive, OneShotLam) = text "(X1)"
      pp_os (IsCheap, NoOneShotInfo) = text "(C?)"
      pp_os (IsExpensive, NoOneShotInfo) = text "(X?)"

mkBotArityType :: [OneShotInfo] -> ArityType
mkBotArityType oss = AT [(IsCheap, os) | os <- oss] botDiv

botArityType :: ArityType
botArityType = mkBotArityType []

topArityType :: ArityType
topArityType = AT [] topDiv

arityTypeArity :: SafeArityType -> Arity
arityTypeArity (AT lams _) = length lams

safeArityType :: ArityType -> SafeArityType
safeArityType at@(AT lams _)
  = case go 0 IsCheap lams of
      Nothing -> at
      Just ar -> AT (take ar lams) topDiv
  where
    go :: Arity -> Cost -> [(Cost, OneShotInfo)] -> Maybe Arity
    go _ _ [] = Nothing
    go ar ch1 ((ch2, os):lams)
      = case (ch1 `addCost` ch2, os) of
          (IsExpensive, NoOneShotInfo) -> Just ar
          (ch, _) -> go (ar + 1) ch lams

infixl 2 `trimArityType`
trimArityType :: Arity -> ArityType -> ArityType
trimArityType max_arity at@(AT lams _)
  | lams `lengthAtMost` max_arity = at
  | otherwise = AT (take max_arity lams) topDiv

-- We Treat ped_bot at True!
data ArityOpts = ArityOpts
  -- { ao_ped_bot :: !Bool } 

exprEtaExpandArity :: HasDebugCallStack => ArityOpts -> CoreExpr -> Maybe SafeArityType
exprEtaExpandArity opts e
  | AT [] _ <- arity_type
  = Nothing
  | otherwise
  = Just arity_type
  where
    arity_type = safeArityType (arityType (findRhsArityEnv opts False) e)

{- *********************************************************************
*                                                                      *
                   findRhsArity
*                                                                      *
********************************************************************* -}

findRhsArity
  :: ArityOpts
  -> RecFlag
  -> CoreId
  -> CoreExpr
  -> (Bool, SafeArityType)
findRhsArity opts is_rec bndr rhs
  | isJoinId bndr
  = (False, join_arity_type)

  | otherwise
  = (arity_increased, non_join_arity_type)
  where
    old_arity = exprArity rhs

    init_env :: ArityEnv
    init_env = findRhsArityEnv opts (isJoinId bndr)

    non_join_arity_type = case is_rec of
                            Recursive -> go 0 botArityType
                            NonRecursive -> step init_env

    arity_increased = arityTypeArity non_join_arity_type > old_arity

    join_arity_type = case is_rec of
                        Recursive -> go 0 botArityType
                        NonRecursive -> trimArityType ty_arity (cheapArityType rhs)

    ty_arity = typeArity (varType bndr)
    use_call_cards = useSiteCallCards bndr

    step :: ArityEnv -> SafeArityType
    step env = trimArityType ty_arity $
               safeArityType $
               combineWithCallCards env (arityType env rhs) use_call_cards

    go :: Int -> SafeArityType -> SafeArityType
    go !n cur_at@(AT lams div)
      | not (isDeadEndDiv div)
      , length lams <= old_arity
      = cur_at
      | next_at == cur_at
      = cur_at
      | otherwise
      = warnPprTrace (debugIsOn && n > 2) "Exciting arity"
        (nest 2 (ppr bndr <+> ppr cur_at <+> ppr next_at $$ ppr rhs)) $
        go (n + 1) next_at
      where
        next_at = step (extendSigEnv init_env bndr cur_at)

combineWithCallCards :: ArityEnv -> ArityType -> [Card] -> ArityType
combineWithCallCards env at@(AT lams div) cards
  | null lams = at
  | otherwise = AT (zip_lams lams oss) div
  where
    oss = map card_to_oneshot cards

    card_to_oneshot n
      | n == C_11
      = OneShotLam
      | otherwise
      = NoOneShotInfo

    zip_lams :: [ATLamInfo] -> [OneShotInfo] -> [ATLamInfo]
    zip_lams lams [] = lams
    zip_lams [] oss
      | isDeadEndDiv div = []
      | otherwise = [ (IsExpensive, OneShotLam)
                    | _ <- takeWhile isOneShotInfo oss ]
    zip_lams ((ch, os1) : lams) (os2 : oss)
      = (ch, os1 `bestOneShot` os2) : zip_lams lams oss

useSiteCallCards :: CoreId -> [Card]
useSiteCallCards bndr
  = call_arity_one_shots `zip_cards` dmd_one_shots
  where
    call_arity_one_shots :: [Card]
    call_arity_one_shots
      | call_arity == 0 = []
      | otherwise = C_1N : replicate (call_arity - 1) C_11

    call_arity = idCallArity bndr

    dmd_one_shots :: [Card]
    dmd_one_shots = case idDemandInfo bndr of
      BotDmd -> []
      _ :* sd -> callCards sd

    zip_cards (n1:ns1) (n2:ns2) = (n1 `glbCard` n2) : zip_cards ns1 ns2
    zip_cards [] ns2 = ns2
    zip_cards ns1 [] = ns1

{- *********************************************************************
*                                                                      *
                   arityType
*                                                                      *
********************************************************************* -}

arityLam :: CoreId -> ArityType -> ArityType
arityLam id (AT oss div) = AT ((IsCheap, one_shot) : oss) div
  where
    one_shot | isDeadEndDiv div = OneShotLam
             | otherwise = idOneShotInfo id

floatIn :: Cost -> ArityType -> ArityType
floatIn ch at@(AT lams div)
  = case lams of
      [] -> at
      (IsExpensive, _) : _ -> at
      (_, os) : lams -> AT ((ch, os) : lams) div

addWork :: ArityType -> ArityType
addWork at@(AT lams div)
  = case lams of
      [] -> at
      lam : lams' -> AT (add_work lam : lams') div

add_work :: ATLamInfo -> ATLamInfo
add_work (_, os) = (IsExpensive, os)

arityApp :: ArityType -> Cost -> ArityType
arityApp (AT ((ch1, _) : oss) div) ch2 = floatIn (ch1 `addCost` ch2) (AT oss div)
arityApp at _ = at

andArityType :: ArityEnv -> ArityType -> ArityType -> ArityType
andArityType env (AT (lam1 : lams1) div1) (AT (lam2 : lams2) div2)
  | AT lams' div' <- andArityType env (AT lams1 div1) (AT lams2 div2)
  = AT ((lam1 `and_lam` lam2) : lams') div'
  where
    and_lam (ch1, os1) (ch2, os2) = (ch1 `addCost` ch2, os1 `bestOneShot` os2)
andArityType env (AT [] div1) at2 = andWithTail env div1 at2
andArityType env at1 (AT [] div2) = andWithTail env div2 at1

andWithTail :: ArityEnv -> Divergence -> ArityType -> ArityType
andWithTail env div1 at2@(AT lams2 _)
  | isDeadEndDiv div1
  = at2
  | otherwise
  = AT [] topDiv

data ArityEnv = AE
  { am_opts :: !ArityOpts
  , am_sigs :: !(IdEnv Zk SafeArityType)
  , am_free_joins :: !Bool
  }

instance Outputable ArityEnv where
  ppr AE{ am_sigs = sigs, am_free_joins = free_joins }
    = text "AE" <+> braces (sep [ text "free joins:" <+> ppr free_joins
                                , text "sigs:" <+> ppr sigs ])

findRhsArityEnv :: ArityOpts -> Bool -> ArityEnv
findRhsArityEnv opts free_joins
  = AE { am_opts = opts
       , am_free_joins = free_joins
       , am_sigs = emptyVarEnv }

freeJoinsOK :: ArityEnv -> Bool
freeJoinsOK AE{ am_free_joins = free_joins } = free_joins

modifySigEnv :: (IdEnv Zk ArityType -> IdEnv Zk ArityType) -> ArityEnv -> ArityEnv
modifySigEnv f env@AE{ am_sigs = sigs } = env { am_sigs = f sigs }
{-# INLINE modifySigEnv #-}

del_sig_env :: CoreId -> ArityEnv -> ArityEnv
del_sig_env id = modifySigEnv (\sigs -> delVarEnv sigs id)
{-# INLINE del_sig_env #-}

del_sig_env_list :: [CoreId] -> ArityEnv -> ArityEnv
del_sig_env_list id = modifySigEnv (\sigs -> delVarEnvList sigs id)
{-# INLINE del_sig_env_list #-}

extendSigEnv :: ArityEnv -> CoreId -> SafeArityType -> ArityEnv
extendSigEnv env id ar_ty = modifySigEnv (\sigs -> extendVarEnv sigs id ar_ty) env

delInScope :: ArityEnv -> CoreId -> ArityEnv
delInScope env id = del_sig_env id env

delInScopeList :: ArityEnv -> [CoreId] -> ArityEnv
delInScopeList env ids = del_sig_env_list ids env

lookupSigEnv :: ArityEnv -> CoreId -> Maybe SafeArityType
lookupSigEnv AE{ am_sigs = sigs } id = lookupVarEnv sigs id

exprCost :: ArityEnv -> CoreExpr -> Maybe CoreType -> Cost
exprCost env e mb_ty
  | myExprIsCheap env e mb_ty = IsCheap
  | otherwise = IsExpensive

myExprIsCheap :: ArityEnv -> CoreExpr -> Maybe CoreType -> Bool
myExprIsCheap AE{ am_opts = opts, am_sigs = sigs } e mb_ty
  = cheap_fun e
  where
    cheap_fun e = exprIsCheapX (myIsCheapApp sigs) False e

myIsCheapApp :: IdEnv Zk SafeArityType -> CheapAppFun
myIsCheapApp sigs fn n_val_args = case lookupVarEnv sigs fn of
  Nothing -> isCheapApp fn n_val_args
  Just (AT lams div)
    | isDeadEndDiv div -> True
    | n_val_args == 0 -> True
    | n_val_args < length lams -> True
    | otherwise -> False

arityType :: HasDebugCallStack => ArityEnv -> CoreExpr -> ArityType
arityType env (Var v)
  | Just at <- lookupSigEnv env v
  = at
  | otherwise
  = assertPpr (freeJoinsOK env || not (isJoinId v)) (ppr v)
    idArityType v
    
arityType env (Cast e _) = arityType env e

arityType env (Lam x _ e)
  | Core.Id b <- x = arityLam b (arityType (delInScope env b) e)
  | otherwise = arityType env e

arityType env (App fun (Type _)) = arityType env fun
arityType env (App fun (KiCo _)) = arityType env fun
arityType env (App fun (Kind _)) = arityType env fun
arityType env (App fun arg)
  = arityApp fun_at arg_cost
  where
    fun_at = arityType env fun
    arg_cost = exprCost env arg Nothing

arityType env (Case scrut bndr _ alts)
  | exprIsDeadEnd scrut || null alts
  = botArityType
  | exprOkForSpeculation scrut
  = alts_type
  | otherwise
  = addWork alts_type
  where
    env' = delInScope env bndr
    arity_type_alt (Alt _ bndrs rhs) = arityType (delInScopeList env' bndrs) rhs
    alts_type = foldr1 (andArityType env) (map arity_type_alt alts)

arityType env (Let (NonRec b rhs) e)
  = floatIn rhs_cost (arityType env' e)
  where
    rhs_cost = exprCost env rhs (Just (varType b))
    env' = extendSigEnv env b (safeArityType (arityType env rhs))

arityType env (Let (Rec prs) e)
  = floatIn (allCosts bind_cost prs) (arityType env' e)
  where
    bind_cost :: (CoreId, CoreExpr) -> Cost
    bind_cost (b, e) = exprCost env' e (Just (varType b))
    env' = foldl extend_rec env prs
    extend_rec :: ArityEnv -> (CoreId, CoreExpr) -> ArityEnv
    extend_rec env (b, _) = extendSigEnv env b $ idArityType b

arityType env (Tick t e)
  | not (tickishIsCode t) = arityType env e

arityType _ _ = topArityType

idArityType :: CoreId -> ArityType
idArityType v
  | strict_sig <- idDmdSig v
  , (ds, div) <- splitDmdSig strict_sig
  , isDeadEndDiv div
  = AT (takeList ds one_shots) div
  | isEmptyTy id_ty
  = botArityType
  | otherwise
  = AT (take (idArity v) one_shots) topDiv
  where
    id_ty = varType v

    one_shots = repeat IsCheap `zip` typeOneShots id_ty

cheapArityType :: HasDebugCallStack => CoreExpr -> ArityType
cheapArityType e = go e
  where
    go (Var v) = idArityType v
    go (Cast e _) = go e
    go (Lam x _ e) | Core.Id v <- x = arityLam v (go e)
                   | otherwise = go e
    go (App e a) | isNonValArg a = go e
                 | otherwise = arity_app a (go e)
    go (Tick t e) | not (tickishIsCode t) = go e
    go (Case _ _ _ alts) | null alts = panic "empty case"
    go _ = topArityType

    arity_app _ at@(AT [] _) = at
    arity_app arg at@(AT ((cost, _) : lams) div)
      | assertPpr (cost == IsCheap) (ppr at $$ ppr arg) $
        isDeadEndDiv div = AT lams div
      | exprIsTrivial arg = AT lams topDiv
      | otherwise = topArityType

exprArity :: CoreExpr -> Arity
exprArity e = go e
  where
    go (Var v) = idArity v
    go (Lam (Core.Id _) _ e) = go e + 1
    go (Lam _ _ e) = go e
    go (Tick t e) | not (tickishIsCode t) = go e
    go (Cast e _) = go e
    go (App e (Type _)) = go e
    go (App e (KiCo _)) = go e
    go (App e (Kind _)) = go e
    go (App f a) | exprIsTrivial a = (go f - 1) `max` 0
    go _ = 0

exprIsDeadEnd :: CoreExpr -> Bool
exprIsDeadEnd e = go 0 e
  where
    go :: Arity -> CoreExpr -> Bool
    go _ Lit{} = False
    go _ Type{} = False
    go _ KiCo{} = False
    go _ Kind{} = False
    go n (App e a) | isValArg a = go (n + 1) e
                   | otherwise = go n e
    go n (Tick _ e) = go n e
    go n (Cast e _) = go n e
    go n (Let _ e) = go n e
    go n (Lam v _ e) | isRuntimeVar v = False
                     | otherwise = go n e
    go _ (Case _ _ _ alts) = null alts
    go n (Var v) | isDeadEndAppSig (idDmdSig v) n = True
                 | isEmptyTy (varType v) = True
                 | otherwise = False

{- *********************************************************************
*                                                                      *
              The main eta-expander
*                                                                      *
********************************************************************* -}

etaExpand :: Arity -> CoreExpr -> CoreExpr
etaExpand n orig_expr = panic "exa_expand in_scope (replicate n NoOneShotInfo) orig_expr"
  -- where
  --   in_scope = {-# SCC "eta_expand:in-scopeX" #-}
  --              panic "mkTermInScopeSets (exprFreeVars orig_expr)"

etaExpandAT :: TermSubstInScope -> SafeArityType -> CoreExpr -> CoreExpr
etaExpandAT in_scope at orig_expr = panic "etaExpandAT"

{- *********************************************************************
*                                                                      *
                Eta reduction
*                                                                      *
********************************************************************* -}

tryEtaReduce
  :: UnVarSet
  -> [(CoreBndr, Maybe CoreMonoKind)]
  -> CoreExpr
  -> SubDemand
  -> Maybe CoreExpr
tryEtaReduce rec_ids bndrs body eval_sd
  = go (reverse bndrs) body (mkReflTyCo (exprType body))
  where
    incoming_arity = count (isRuntimeVar . fst) bndrs

    go :: [(CoreBndr, Maybe CoreMonoKind)] -> CoreExpr -> TypeCoercion Zk -> Maybe CoreExpr
    go bs (Cast e co1) co2 = go bs e (co1 `mkTyTransCo` co2)
    go bs (Tick t e) co
      | tickishFloatable t
      = (Tick t) <$> go bs e co
    go (b : bs) (App fun arg) co
      | Just (co', ticks) <- ok_arg b arg co (exprType fun)
      = (flip (foldr mkTick) ticks) <$> go bs fun co'
    go remaining_bndrs fun co
      | all (not. isRuntimeVar . fst) remaining_bndrs
      , remaining_bndrs `ltLength` bndrs
      , ok_fun fun
      , let used_vars = case (exprFreeVars fun, varsOfTyCo co) of
              ((ids1, tcvs1, tvs1, kcvs1, kvs1), (tvs2, kcvs2, kvs2))
                -> ( ids1
                   , tcvs1 --`unionVarSet` tcvs2
                   , tvs1 `unionVarSet` tvs2
                   , kcvs1 `unionVarSet` kcvs2
                   , kvs1 `unionVarSet` kvs2 )
            reduced_bndrs = mkCoreBndrVarSets (fst <$> dropList remaining_bndrs bndrs)
      , used_vars `disjointCoreVarSets` reduced_bndrs
      = Just (mkCoreLams (reverse remaining_bndrs) (mkCast fun co))
    go _ _ _ = Nothing

    ok_fun (App fun (Type {})) = ok_fun fun
    ok_fun (App fun (KiCo {})) = ok_fun fun
    ok_fun (App fun (Kind {})) = ok_fun fun
    ok_fun (Cast fun _) = ok_fun fun
    ok_fun (Tick _ expr) = ok_fun expr
    ok_fun (Var fun_id) = is_eta_reduction_sound fun_id
    ok_fun _ = False

    is_eta_reduction_sound fun
      | fun `elemUnVarSet` rec_ids
      = False
      | cantEtaReduceFun fun
      = False
      | otherwise
      = fun_arity fun >= incoming_arity
        || all_calls_with_arity incoming_arity
        || all ok_lam bndrs

    all_calls_with_arity n = fstOf3 (peelManyCalls n eval_sd)

    fun_arity fun
      | arity > 0 = arity
      | isEvaldUnfolding (idUnfolding fun) = 1
      | otherwise = 0
      where
        arity = idArity fun

    ok_lam = not . isRuntimeVar . fst

    ok_arg
      :: (CoreBndr, Maybe CoreMonoKind)
      -> CoreExpr
      -> TypeCoercion Zk
      -> CoreType 
      -> Maybe (TypeCoercion Zk, [CoreTickish])
    ok_arg (Tv bndr, _) (Type arg_ty) co fun_ty
      | Just tv <- getTyVar_maybe arg_ty
      , bndr == tv = case splitForAllForAllTyBinder_maybe fun_ty of
          Just (Bndr _ vis, _) -> Just (fco, [])
            where !fco = mkForAllCo tv vis coreTyLamForAllTyFlag kco co
                  kco = mkReflKiCo (varKind tv)
          Nothing -> pprPanic "tryEtaReduce: type arg to non-forall type"
                     (text "fun:" <+> ppr bndr
                      $$ text "arg:" <+> ppr arg_ty
                      $$ text "fun_ty:" <+> ppr fun_ty)
    ok_arg (KCv bndr, _) (KiCo arg_co) co fun_ty = panic "unfinished"
    ok_arg (Kv bndr, _) (Kind arg_ki) co fun_ty = panic "unfinished"
    ok_arg (Core.Id bndr, _) (Var v) co fun_ty
      | bndr == v
      , Just (_, fki, _) <- splitFunTy_maybe fun_ty
      = Just (mkTyFunCo (mkReflKiCo fki) (mkReflTyCo (varType bndr)) co, [])
    ok_arg bndr (Cast e co_arg) co fun_ty = panic "unfinished"
    ok_arg bndr (Tick t arg) co fun_ty = panic "unfinished"
    ok_arg _ _ _ _ = Nothing

cantEtaReduceFun :: CoreId -> Bool
cantEtaReduceFun fun
  = hasNoBinding fun
    || isJoinId fun
    -- TODO: check if there is an issue since all my stuff is CBV!
    -- GHC does NOT eta reduce CBV workers

{- *********************************************************************
*                                                                      *
                The "push rules"
*                                                                      *
********************************************************************* -}

pushCoArgs :: TypeCoercion Zk -> [CoreArg] -> Maybe ([CoreArg], MTypeCoercion Zk)
pushCoArgs co [] = return ([], MCo co)
pushCoArgs co (arg:args) = do panic "pushCoArgs"
  -- (arg', m_co1) <- pushCoArg co arg
  -- case m_co1 of
  --   MCo co1 -> do (args', m_co2) <- pushCoArgs co1 args
  --                 return (arg':args', m_co2)
  --   MRefl -> return (arg':args, MRefl)

-- pushCoArg :: TypeCoercion Zk -> CoreArg -> Maybe (CoreArg, MTypeCoercion Zk)
-- pushCoArg co arg
--   | Type ty <- arg
--   = do (ty', m_co') <- pushCoTyArg co ty
--        return (Type ty', m_co')
--   | Kind ki <- arg
--   = do (ki', m_co') <- pushCoKiArg co ki
--        return (Kind ki', m_co')
--   | otherwise
--   = do (arg_mco, m_co') <- pushCoValArg co
--        let arg_mco' = checkReflexiveMCo arg_mco
--        return (arg `mkCastMCo` arg_mco', m_co')


pushCoDataCon
  :: DataCon Zk
  -> [CoreExpr]
  -> MTypeCoercion Zk
  -> Maybe (DataCon Zk, [CoreType], [CoreExpr])
pushCoDataCon = panic "pushCoDataCon"

{- *********************************************************************
*                                                                      *
                Join points
*                                                                      *
********************************************************************* -}

etaExpandToJoinPoint :: JoinArity -> CoreExpr -> ([(CoreBndr, Maybe CoreMonoKind)], CoreExpr)
etaExpandToJoinPoint join_arity expr
  = go join_arity [] expr
  where
    go 0 rev_bs e = (reverse rev_bs, e)
    go n rev_bs (Lam b k e) = go (n - 1) ((b, k) : rev_bs) e
    go n rev_bs e = case etaBodyForJoinPoint n e of
                      (bs, e') -> (reverse rev_bs ++ bs, e')

etaExpandToJoinPointRule :: JoinArity -> CoreRule -> CoreRule
etaExpandToJoinPointRule _ rule@BuiltinRule{}
  = warnPprTrace True "Can't eta-expand built-in rule:" (ppr rule)
    rule
etaExpandToJoinPointRule join_arity rule@Rule{ ru_bndrs = bndrs, ru_rhs = rhs, ru_args = args }
  | need_args == 0
  = rule
  | need_args < 0
  = pprPanic "etaExpandToJoinPointRule" (ppr join_arity $$ ppr rule)
  | otherwise
  = rule { ru_bndrs = bndrs ++ new_bndrs
         , ru_args = args ++ new_args
         , ru_rhs = new_rhs }
  where
    need_args = join_arity - length args
    (new_bndrs1, new_rhs) = etaBodyForJoinPoint need_args rhs
    new_bndrs = fst <$> new_bndrs1
    new_args = bndrsToCoreExprs new_bndrs

etaBodyForJoinPoint :: Int -> CoreExpr -> ([(CoreBndr, Maybe CoreMonoKind)], CoreExpr) 
etaBodyForJoinPoint need_args body
  = panic "etaBodyForJoinPoint"
