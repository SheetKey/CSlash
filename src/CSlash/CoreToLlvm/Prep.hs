{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BangPatterns #-}

{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module CSlash.CoreToLlvm.Prep where

{-
Our core prep phase is similar to GHC, but differs in a number of ways.

Like GHC, we
1. saturate constructor and primop applications.
2. Convert to A-normal form (function arguments are always variables)
3. Ensure value lambdas are only on the RHS of a binding.  
4. ANF-isation results in bindings that we float out.
5. Clone all local Ids.
6. Tick stuff
7. CCs
8. Eliminate some magic Ids (we currently have none)

Differences:
1. At this point, we drop the 'let-can-float' invariant used during Core2Core. Thus, we convert
'case E of x -> ..' to 'let x = E in ..'
2. Eliminate the use of type synonyms.
-}

import Prelude hiding ((<>))

import CSlash.Platform

import CSlash.Driver.Flags

import CSlash.Unit

import CSlash.Builtin.Names
-- import CSlash.Builtin.PrimOps
-- import CSlash.Builtin.PrimOps.Ids
import CSlash.Builtin.Types
import CSlash.Builtin.Types.Prim

import CSlash.Core.Utils
import CSlash.Core.Opt.Arity
import CSlash.Core.Lint ( EndPassConfig(..), endPassIO )
import CSlash.Core as C
import CSlash.Core.Subst
import CSlash.Core.Make hiding( FloatBind(..) )   -- We use our own FloatBind here
import CSlash.Core.Type
import CSlash.Core.TyCon
import CSlash.Core.DataCon
import CSlash.Core.Opt.OccurAnal

import CSlash.Data.Maybe
import CSlash.Data.OrdList
import CSlash.Data.FastString
import CSlash.Data.Graph.UnVar

import CSlash.Utils.Error
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Outputable
import CSlash.Utils.Monad  ( mapAccumLM )
import CSlash.Utils.Logger
import CSlash.Utils.Trace

import CSlash.Types.Demand
import CSlash.Types.Var
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
-- import CSlash.Types.Var.Id.Make ( realWorldPrimId )
import CSlash.Types.Basic
import CSlash.Types.Name   ( NamedThing(..), nameSrcSpan, isInternalName )
import CSlash.Types.SrcLoc ( SrcSpan(..), realSrcLocSpan, mkRealSrcLoc )
import CSlash.Types.Literal
import CSlash.Types.Tickish
import CSlash.Types.Unique.Supply

import qualified Data.ByteString as BS
import qualified Data.ByteString.Builder as BB
import Data.ByteString.Builder.Prim

import Control.Monad

type CpeArg = CoreExpr
type CpeApp = CoreExpr
type CpeBody = CoreExpr
type CpeRhs = CoreExpr

{- *********************************************************************
*                                                                      *
                Top level stuff
*                                                                      *
********************************************************************* -}

data CorePrepPgmConfig = CorePrepPgmConfig
  { cpPgm_endPassConfig :: !EndPassConfig
  , cpPgm_generateDebugInfo :: !Bool
  }

corePrepPgm
  :: Logger
  -> CorePrepConfig
  -> CorePrepPgmConfig
  -> Module
  -> ModLocation
  -> CoreProgram
  -> IO CoreProgram
corePrepPgm logger cp_cfg pgm_cfg this_mod mod_loc binds
  = withTiming logger (text "CorePrep" <+> brackets (ppr this_mod))
    (\a -> a `seqList` ()) $
    do us <- mkSplitUniqSupply 's'
       let initialCorePrepEnv = mkInitialCorePrepEnv cp_cfg

           binds_out = initUs_ us $ do
             floats1 <- corePrepTopBinds initialCorePrepEnv binds
             return (deFloatTop floats1)
       endPassIO logger (cpPgm_endPassConfig pgm_cfg) binds_out []
       return binds_out

corePrepExpr :: Logger -> CorePrepConfig -> CoreExpr -> IO CoreExpr
corePrepExpr logger config expr
  = withTiming logger (text "CorePrep [expr]") (\e -> e `seq` ()) $ do
      us <- mkSplitUniqSupply 's'
      let initialCorePrepEnv = mkInitialCorePrepEnv config
          new_expr = initUs_ us (cpeBodyNF initialCorePrepEnv expr)
      putDumpFileMaybe logger Opt_D_dump_prep "CorePrep" FormatCore (ppr new_expr)
      return new_expr

corePrepTopBinds :: CorePrepEnv -> [CoreBind] -> UniqSM Floats
corePrepTopBinds initialCorePrepEnv binds
  = go initialCorePrepEnv binds
  where
    go _ [] = return emptyFloats
    go env (bind:binds) = do
      (env', floats, maybe_new_bind) <- cpeBind TopLevel env bind
      massert (isNothing maybe_new_bind)
      floatss <- go env' binds
      return (floats `zipFloats` floatss)

{- *********************************************************************
*                                                                      *
                The main code
*                                                                      *
********************************************************************* -}

cpeBind
  :: TopLevelFlag -> CorePrepEnv -> CoreBind -> UniqSM (CorePrepEnv, Floats, Maybe CoreBind)
cpeBind top_lvl env (NonRec bndr rhs)
  | not (isJoinId bndr)
  = do (env1, bndr1) <- cpCloneBndr env bndr
       let dmd = idDemandInfo bndr
       (floats, rhs1) <- cpePair top_lvl NonRecursive dmd env bndr1 rhs
       let triv_rhs = exprIsTrivial rhs1
           env2 | triv_rhs = extendCorePrepEnvExpr env1 bndr rhs1
                | otherwise = env1
           floats1
             | triv_rhs, isInternalName (varName bndr)
             = floats
             | otherwise
             = snocFloat floats new_float
           new_float = mkNonRecFloat env bndr1 rhs1
       return (env2, floats1, Nothing)
  | otherwise
  = assert (not (isTopLevel top_lvl)) $ do
      (_, bndr1) <- cpCloneBndr env bndr
      (bndr2, rhs1) <- cpeJoinPair env bndr1 rhs
      return ( extendCorePrepEnv env bndr bndr2
             , emptyFloats
             , Just (NonRec bndr2 rhs1))

cpeBind top_lvl env (Rec pairs)
  | not (isJoinId (head bndrs))
  = do (env, bndrs1) <- cpCloneBndrs env bndrs
       let env' = enterRecGroupRHSs env bndrs1
       stuff <- zipWithM (cpePair top_lvl Recursive topDmd env') bndrs1 rhss
       let (zipManyFloats -> floats, rhss1) = unzip stuff
           is_lit (Float (NonRec _ rhs) TopLvlFloatable) = panic "exprIsTickedString rhs"
           is_lit _ = False
           (string_floats, top) = partitionOL is_lit (fs_binds floats)
           floats' = floats { fs_binds = top }
           all_pairs = foldrOL add_float (bndrs1 `zip` rhss1) (getFloats floats')
       return ( extendCorePrepEnvList env (bndrs `zip` bndrs1)
              , snocFloat (emptyFloats { fs_binds = string_floats })
                (Float (Rec all_pairs) TopLvlFloatable)
              , Nothing )

  | otherwise
  = do (env, bndrs1) <- cpCloneBndrs env bndrs
       let env' = enterRecGroupRHSs env bndrs1
       pairs1 <- zipWithM (cpeJoinPair env') bndrs1 rhss
       let bndrs2 = map fst pairs1
       return ( extendCorePrepEnvList env (bndrs `zip` bndrs2)
              , emptyFloats
              , Just (Rec pairs1) )
  where
    (bndrs, rhss) = unzip pairs

    add_float (Float bind _) prs2
      = case bind of
          NonRec x e -> (x, e) : prs2
          Rec prs1 -> prs1 ++ prs2
    add_float f _ = pprPanic "cpeBind" (ppr f)

cpePair
  :: TopLevelFlag
  -> RecFlag
  -> Demand
  -> CorePrepEnv
  -> OutId
  -> CoreExpr
  -> UniqSM (Floats, CpeRhs)
cpePair top_lvl is_rec dmd env bndr rhs
  = assert (not (isJoinId bndr)) $ do
      (floats1, rhs1) <- cpeRhsE env rhs
      let dec = want_float_from_rhs floats1 rhs1
      (floats2, rhs2) <- executeFloatDecision dec floats1 rhs1

      (floats3, rhs3)
        <- if manifestArity rhs1 <= arity
           then return (floats2, cpeEtaExpand arity rhs2)
           else warnPprTrace True "CorePrep: silly extra arguments:" (ppr bndr) $
                do v <- newVar (varType bndr)
                   let float = mkNonRecFloat env v rhs2
                   return ( snocFloat floats2 float
                          , cpeEtaExpand arity (Var v))

      let (floats4, rhs4) = wrapTicks floats3 rhs3

      return (floats4, rhs4)
  where
    arity = idArity bndr

    want_float_from_rhs floats rhs
      | isTopLevel top_lvl = wantFloatTop floats
      | otherwise = wantFloatLocal is_rec dmd floats rhs

cpeJoinPair
  :: CorePrepEnv
  -> JoinId
  -> CoreExpr
  -> UniqSM (JoinId, CpeRhs)
cpeJoinPair env bndr rhs
  = assert (isJoinId bndr) $ 
    do let JoinPoint join_arity = idJoinPointHood bndr
           (bndrs, body) = collectNBinders join_arity rhs
       (env', bndrs') <- cpCloneLamBndrs env bndrs
       body' <- cpeBodyNF env' body
       let rhs' = mkCoreLams bndrs' body'
           bndr' = bndr `setIdUnfolding` evaldUnfolding
                   `setIdArity` count (isRuntimeVar . fst) bndrs
       return (bndr', rhs')

cpeRhsE :: CorePrepEnv -> CoreExpr -> UniqSM (Floats, CpeRhs)
cpeRhsE env (Type ty) = return (emptyFloats, Type (cpSubstTy env ty))
cpeRhsE env (KiCo co) = return (emptyFloats, KiCo (cpSubstKiCo env co))
cpeRhsE env (Kind ki) = return (emptyFloats, Kind (cpSubstMonoKi env ki))
cpeRhsE env expr@Lit{} = return (emptyFloats, expr)

cpeRhsE env expr@Var{} = cpeApp env expr
cpeRhsE env expr@App{} = cpeApp env expr

cpeRhsE env (Let bind body) = do
  (env', bind_floats, maybe_bind') <- cpeBind NotTopLevel env bind
  (body_floats, body') <- cpeRhsE env' body
  let expr' = case maybe_bind' of
                Just bind' -> Let bind' body'
                Nothing -> body'
  return (bind_floats `appFloats` body_floats, expr')

cpeRhsE env (Tick tickish expr)
  | tickishFloatable tickish
  = do (floats, body) <- cpeRhsE env expr
       return (FloatTick tickish `consFloat` floats, body)
  | otherwise
  = do body <- cpeBodyNF env expr
       return (emptyFloats, mkTick tickish body)

cpeRhsE env (Cast expr co) = do
  (floats, expr') <- cpeRhsE env expr
  return (floats, Cast expr' (cpSubstTyCo env co))

cpeRhsE env expr@Lam{} = do
  let (bndrs, body) = collectBinders expr
  (env', bndrs') <- cpCloneLamBndrs env bndrs
  body' <- cpeBodyNF env' body
  return (emptyFloats, mkCoreLams bndrs' body')

cpeRhsE env (Case scrut bndr ty alts) = do
  (floats, scrut') <- cpeBody env scrut
  (env', bndr2) <- cpCloneBndr env bndr
  let alts'
        | cp_catchNonexhaustiveCases $ cpe_config env
        , not (altsAreExhaustive alts)
        = addDefault alts (Just err)
        | otherwise = alts
        where err = panic "mkImpossibleExpr"-- ty "cpeRhsE: missing case alternate"
  alts'' <- mapM (sat_alt env') alts'

  case alts'' of
    -- This is where we drop the let-can-float invariant
    -- and turn 'case x of y DEFAULT -> ..' into 'let y = x in ..'
    [Alt DEFAULT _ rhs]
      -> let float = mkCaseFloat bndr2 scrut'
         in return (snocFloat floats float, rhs)
    _ -> return (floats, Case scrut' bndr2 (cpSubstTy env ty) alts'')

  where
    sat_alt env (Alt con bs rhs) = do
      (env2, bs') <- cpCloneBndrs env bs
      rhs' <- cpeBodyNF env2 rhs
      return (Alt con bs' rhs')

cpeBodyNF :: CorePrepEnv -> CoreExpr -> UniqSM CpeBody
cpeBodyNF env expr = do
  (floats, body) <- cpeBody env expr
  return (wrapBinds floats expr)

cpeBody :: CorePrepEnv -> CoreExpr -> UniqSM (Floats, CpeBody)
cpeBody env expr = do
  (floats1, rhs) <- cpeRhsE env expr
  (floats2, body) <- rhsToBody rhs
  return (floats1 `appFloats` floats2, body)

rhsToBody :: CpeRhs -> UniqSM (Floats, CpeBody)
rhsToBody (Tick t expr)
  | tickishScoped t == NoScope
  = do (floats, expr') <- rhsToBody expr
       return (floats, mkTick t expr')
rhsToBody (Cast e co)
  = do (floats, e') <- rhsToBody e
       return (floats, Cast e' co)
rhsToBody expr@Lam{}
  | all (isNonRuntimeVar . fst) bndrs
  = return (emptyFloats, expr)
  | otherwise
  = do let rhs = cpeEtaExpand (exprArity expr) expr
       fn <- newVar (exprType rhs)
       let float = Float (NonRec fn rhs) TopLvlFloatable
       return (unitFloat float, Var fn)
  where (bndrs, _) = collectBinders expr
rhsToBody expr = return (emptyFloats, expr)

data ArgInfo
  = AIApp CoreArg
  | AICast CoreTypeCoercion
  | AITick CoreTickish

cpeApp :: CorePrepEnv -> CoreExpr -> UniqSM (Floats, CpeRhs)
cpeApp top_env expr = do
  let (terminal, args) = collect_args expr
  cpe_app top_env terminal args
  where
    collect_args :: CoreExpr -> (CoreExpr, [ArgInfo])
    collect_args e = go e []
      where
        go (App fun arg) as = go fun (AIApp arg : as)
        go (Cast fun co) as = go fun (AICast co : as)
        go (Tick tickish fun) as
          | Var vh <- head
          , Var head' <- lookupCorePrepEnv top_env vh
          , etaExpansionTick head' tickish
          = (head, as')
          where (head, as') = go fun (AITick tickish : as)
        go terminal as = (terminal, as)

    cpe_app
      :: CorePrepEnv
      -> CoreExpr
      -> [ArgInfo]
      -> UniqSM (Floats, CpeRhs)
    cpe_app env (Var v) args = do
      v1 <- fiddleCCall v
      let e2 = lookupCorePrepEnv env v1
          hd = getIdFromTrivialExpr_maybe e2
          min_arity = case hd of
            Just v_hd -> if hasNoBinding v_hd then Just $! (idArity v_hd) else Nothing
            Nothing -> Nothing
      (app, floats, unsat_ticks) <- rebuild_app env args e2 emptyFloats dmds min_arity
      mb_saturate hd app floats unsat_ticks depth
      where
        depth = val_args args
        dmds = case idDmdSig v of
                 DmdSig (DmdType _ demands)
                   | listLengthCmp demands depth /= GT -> demands
                   | otherwise -> []

    cpe_app env fun [] = cpeRhsE env fun

    cpe_app env fun args = do
      (fun_floats, fun') <- cpeArg env evalDmd fun
      (app, floats, unsat_ticks) <- rebuild_app env args fun' fun_floats [] Nothing
      mb_saturate Nothing app floats unsat_ticks (val_args args)

    val_args :: [ArgInfo] -> Int
    val_args args = go args 0
      where
        go [] !n = n
        go (info: infos) n = case info of
          AICast {} -> go infos n
          AITick tickish
            | tickishFloatable tickish -> go infos n
            | otherwise -> n
          AIApp e -> go infos n'
            where
              !n' | isNonValArg e = n
                  | otherwise = n + 1

    mb_saturate head app floats unsat_ticks depth
      = case head of
          Just fn_id -> do sat_app <- maybeSaturate fn_id app depth unsat_ticks
                           return (floats, sat_app)
          Nothing -> do massert (null unsat_ticks)
                        return (floats, app)
      
    rebuild_app
      :: CorePrepEnv
      -> [ArgInfo]
      -> CpeApp
      -> Floats
      -> [Demand]
      -> Maybe Arity
      -> UniqSM (CpeApp, Floats, [CoreTickish])
    rebuild_app env args app floats ss req_depth
      = rebuild_app' env args app floats ss [] (fromMaybe 0 req_depth)
      
    rebuild_app'
      :: CorePrepEnv
      -> [ArgInfo]
      -> CpeApp
      -> Floats
      -> [Demand]
      -> [CoreTickish]
      -> Int
      -> UniqSM (CpeApp, Floats, [CoreTickish])
    rebuild_app' _ [] app floats ss rt_ticks !_
      = assertPpr (null ss) (ppr ss)
        return (app, floats, rt_ticks)
    rebuild_app' env (a:as) fun' floats ss rt_ticks req_depth
      = case a of
          _ | not (null rt_ticks)
            , req_depth <= 0
            -> let tick_fun = foldr mkTick fun' rt_ticks
               in rebuild_app' env (a:as) tick_fun floats ss rt_ticks req_depth

          AIApp (Type arg_ty)
            -> rebuild_app' env as (App fun' (Type arg_ty')) floats ss rt_ticks req_depth
            where arg_ty' = cpSubstTy env arg_ty
          AIApp (KiCo arg_co)
            -> rebuild_app' env as (App fun' (KiCo arg_co')) floats ss rt_ticks req_depth
            where arg_co' = cpSubstKiCo env arg_co
          AIApp (Kind arg_ki)
            -> rebuild_app' env as (App fun' (Kind arg_ki')) floats ss rt_ticks req_depth
            where arg_ki' = cpSubstMonoKi env arg_ki

          AIApp arg -> do
            let (ss1, ss_rest)
                  = case ss of
                      (ss1 : ss_rest) -> (ss1, ss_rest)
                      [] -> (topDmd, [])

            (fs, arg') <- cpeArg top_env ss1 arg
            rebuild_app' env as (App fun' arg')
                         (fs `zipFloats` floats) ss_rest rt_ticks (req_depth - 1)

          AICast co
            -> rebuild_app' env as (Cast fun' co') floats ss rt_ticks req_depth
            where co' = cpSubstTyCo env co

          AITick tickish
            | tickishPlace tickish == PlaceRuntime
            , req_depth > 0
            -> assert (isProfTick tickish) $
               rebuild_app' env as fun' floats ss (tickish : rt_ticks) req_depth
            | otherwise
            -> rebuild_app' env as fun' (snocFloat floats (FloatTick tickish)) ss rt_ticks
               req_depth
              
cpeArg
  :: CorePrepEnv
  -> Demand
  -> CoreArg
  -> UniqSM (Floats, CpeArg)
cpeArg env dmd arg = do
  (floats1, arg1) <- cpeRhsE env arg
  let arg_ty = exprType arg1
      dec = wantFloatLocal NonRecursive dmd floats1 arg1
  (floats2, arg2) <- executeFloatDecision dec floats1 arg1

  if exprIsTrivial arg2
    then return (floats2, arg2)
    else do v <- (`setIdDemandInfo` dmd) <$> newVar arg_ty
            let arity = cpeArgArity env dec floats1 arg2
                arg3 = cpeEtaExpand arity arg2
                arg_float = mkNonRecFloat env v arg3
            return (snocFloat floats2 arg_float, varToCoreExpr v)

cpeArgArity :: CorePrepEnv -> FloatDecision -> Floats -> CoreArg -> Arity
cpeArgArity env float_decision floats1 arg
  | FloatNone <- float_decision
  , not (isEmptyFloats floats1)
  , fs_info floats1 `floatsAtLeastAsFarAs` panic "WHAT"
  = 0

  | Just ao <- cp_arityOpts (cpe_config env)
  , not (eta_would_wreck_join arg)
  = case exprEtaExpandArity ao arg of
      Nothing -> 0
      Just at -> arityTypeArity at

  | otherwise
  = exprArity arg

eta_would_wreck_join :: CoreExpr -> Bool
eta_would_wreck_join (Let bs e) = isJoinBind bs || eta_would_wreck_join e
eta_would_wreck_join (Lam _ _ e) = eta_would_wreck_join e
eta_would_wreck_join (Cast e _) = eta_would_wreck_join e
eta_would_wreck_join (Tick _ e) = eta_would_wreck_join e
eta_would_wreck_join (Case _ _ _ alts) = any eta_would_wreck_join (rhssOfAlts alts)
eta_would_wreck_join _ = False

-- TODO: this may be a very important function to change:
-- In GHC, it decides to eta expand base on CBVMarks.
-- Only join points and workers have CBVMarks in GHC.
-- In CSlash, ALL functions are CBV.
-- GHC note [Use CBV semantics only for join points and workers] in Types.Id.Info if relevant.
maybeSaturate :: CoreId -> CpeApp -> Int -> [CoreTickish] -> UniqSM CpeRhs
maybeSaturate fn expr n_args unsat_ticks
  | hasNoBinding fn
  = return $ wrapLamBody (\body -> foldr mkTick body unsat_ticks) sat_expr

  -- | mark_arity > 0
  -- , not applied_marks
  -- = assertPpr
  --   (not (isJoinId fn))
  --   (ppr fn $$ text "expr:" <+> ppr expr $$ text "n_args:" <+> ppr n_args $$
  --    text "join_arity" <+> ppr (idJoinPointHood fn) $$
  --    text "fn_arity" <+> ppr fn_arity)
  --   $ return sat_expr

  | otherwise
  = assert (null unsat_ticks) $ return expr
  where
    fn_arity = idArity fn
    excess_arity = fn_arity - n_args
    sat_expr = cpeEtaExpand excess_arity expr

cpeEtaExpand :: Arity -> CpeRhs -> CpeRhs
cpeEtaExpand arity expr
  | arity == 0 = expr
  | otherwise = etaExpand arity expr

{- *********************************************************************
*                                                                      *
                Floats
*                                                                      *
********************************************************************* -}

data FloatInfo
  = TopLvlFloatable
  | StrictContextFloatable
  deriving Eq

instance Outputable FloatInfo where
  ppr TopLvlFloatable = text "top-lvl"
  ppr StrictContextFloatable = text "str-ctx"

data FloatingBind
  = Float !CoreBind !FloatInfo
  | FloatTick CoreTickish

data Floats = Floats
  { fs_info :: !FloatInfo
  , fs_binds :: !(OrdList FloatingBind)
  }

instance Outputable FloatingBind where
  ppr (Float b fi) = text "Let" <+> ppr fi <+> ppr b
  ppr (FloatTick t) = ppr t

instance Outputable Floats where
  ppr (Floats info binds) = text "Floats" <> brackets (ppr info) <> braces (ppr binds)

lubFloatInfo :: FloatInfo -> FloatInfo -> FloatInfo
lubFloatInfo StrictContextFloatable _ = StrictContextFloatable
lubFloatInfo _ StrictContextFloatable = StrictContextFloatable
lubFloatInfo TopLvlFloatable TopLvlFloatable = TopLvlFloatable

floatsAtLeastAsFarAs :: FloatInfo -> FloatInfo -> Bool
floatsAtLeastAsFarAs l r = l `lubFloatInfo` r == r

emptyFloats :: Floats
emptyFloats = Floats TopLvlFloatable nilOL

isEmptyFloats :: Floats -> Bool
isEmptyFloats (Floats _ b) = isNilOL b

getFloats :: Floats -> OrdList FloatingBind
getFloats = fs_binds

unitFloat :: FloatingBind -> Floats
unitFloat = snocFloat emptyFloats

floatInfo :: FloatingBind -> FloatInfo
floatInfo (Float _ info) = info
floatInfo FloatTick{} = TopLvlFloatable

snocFloat :: Floats -> FloatingBind -> Floats
snocFloat floats fb =
  Floats { fs_info = lubFloatInfo (fs_info floats) (floatInfo fb)
         , fs_binds = fs_binds floats `snocOL` fb }

consFloat :: FloatingBind -> Floats -> Floats
consFloat fb floats =
  Floats { fs_info = lubFloatInfo (fs_info floats) (floatInfo fb)
         , fs_binds = fb `consOL` fs_binds floats }

appFloats :: Floats -> Floats -> Floats
appFloats outer inner =
  Floats { fs_info = lubFloatInfo (fs_info outer) (fs_info inner)
         , fs_binds = fs_binds outer `appOL` fs_binds inner }
      
zipFloats :: Floats -> Floats -> Floats
zipFloats = appFloats

zipManyFloats :: [Floats] -> Floats
zipManyFloats = foldr zipFloats emptyFloats

-- TODO: important to check this: should we do LetBound here?
mkCaseFloat :: CoreId -> CpeRhs -> FloatingBind
mkCaseFloat bndr scrut = Float (NonRec bndr scrut) info
  where
    info
      | panic "exprIsTickedString scrut" = TopLvlFloatable
      | otherwise = StrictContextFloatable

mkNonRecFloat :: CorePrepEnv -> CoreId -> CpeRhs -> FloatingBind
mkNonRecFloat env bndr rhs
  = Float (NonRec bndr rhs) info
  where
    info
      | is_data_con bndr = TopLvlFloatable
      | panic "exprIsTickedString rhs" = TopLvlFloatable
      | otherwise = StrictContextFloatable

    is_data_con = isJust . isDataConId_maybe

wrapBinds :: Floats -> CpeBody -> CpeBody
wrapBinds floats body = foldrOL mk_bind body (getFloats floats)
  where
    mk_bind f@(Float bind _) body
      = Let bind body
    mk_bind (FloatTick tickish) body
      = mkTick tickish body

deFloatTop :: Floats -> [CoreBind]
deFloatTop floats = foldrOL get [] (getFloats floats)
  where
    get (Float b TopLvlFloatable) bs = get_bind b : bs
    get b _ = pprPanic "deFloatTop" (ppr b)

    get_bind (NonRec x e) = NonRec x (occurAnalyzeExpr e)
    get_bind (Rec xes) = Rec [(x, occurAnalyzeExpr e) | (x, e) <- xes]

data FloatDecision
  = FloatNone
  | FloatAll

executeFloatDecision :: FloatDecision -> Floats -> CpeRhs -> UniqSM (Floats, CpeRhs)
executeFloatDecision dec floats rhs
  = case dec of
      FloatAll -> return (floats, rhs)
      FloatNone
        | isEmptyFloats floats -> return (emptyFloats, rhs)
        | otherwise -> do (floats', body) <- rhsToBody rhs
                          return (emptyFloats, wrapBinds floats $ wrapBinds floats' body)

wantFloatTop :: Floats -> FloatDecision
wantFloatTop fs
  | fs_info fs `floatsAtLeastAsFarAs` TopLvlFloatable = FloatAll
  | otherwise = FloatNone

wantFloatLocal :: RecFlag -> Demand -> Floats -> CpeRhs -> FloatDecision
wantFloatLocal _ _ _ _ = FloatAll
  
{- *********************************************************************
*                                                                      *
                Cloning
*                                                                      *
********************************************************************* -}

data CorePrepConfig = CorePrepConfig
  { cp_catchNonexhaustiveCases :: !Bool
  , cp_platform :: Platform
  , cp_arityOpts :: !(Maybe ArityOpts)
  , cp_specEval :: !Bool -- TODO: I think this is unused
  }

data CorePrepEnv = CPE
  { cpe_config :: !CorePrepConfig
  , cpe_subst :: CoreSubst
  , cpe_rec_ids :: UnVarSet
  }

mkInitialCorePrepEnv :: CorePrepConfig -> CorePrepEnv
mkInitialCorePrepEnv cfg = CPE
  { cpe_config = cfg
  , cpe_subst = emptySubst
  , cpe_rec_ids = emptyUnVarSet
  }

extendCorePrepEnv :: CorePrepEnv -> CoreId -> CoreId -> CorePrepEnv
extendCorePrepEnv cpe@CPE{ cpe_subst = subst } id id'
  = cpe { cpe_subst = subst2 }
  where
    subst1 = extendTermSubstInScopeId subst id'
    subst2 = extendIdSubst subst1 id (Var id')

extendCorePrepEnvList :: CorePrepEnv -> [(CoreId, CoreId)] -> CorePrepEnv
extendCorePrepEnvList cpe@CPE{ cpe_subst = subst } prs
  = cpe { cpe_subst = subst2 }
  where
    subst1 = extendTermSubstInScopeListId subst (map snd prs)
    subst2 = extendIdSubstList subst1 [(id, Var id') | (id, id') <- prs]

extendCorePrepEnvExpr :: CorePrepEnv -> CoreId -> CoreExpr -> CorePrepEnv
extendCorePrepEnvExpr cpe id expr
  = cpe { cpe_subst = extendIdSubst (cpe_subst cpe) id expr }
    
lookupCorePrepEnv :: CorePrepEnv -> CoreId -> CoreExpr
lookupCorePrepEnv cpe id = case lookupIdSubst_maybe (cpe_subst cpe) id of
  Just e -> e
  Nothing -> Var id

enterRecGroupRHSs :: CorePrepEnv -> [OutId] -> CorePrepEnv
enterRecGroupRHSs env grp
  = env { cpe_rec_ids = extendUnVarSetList grp (cpe_rec_ids env) }

cpSubstTy :: CorePrepEnv -> CoreType -> CoreType
cpSubstTy CPE{ cpe_subst = subst } ty = substTy subst ty

cpSubstTyCo :: CorePrepEnv -> CoreTypeCoercion -> CoreTypeCoercion
cpSubstTyCo CPE{ cpe_subst = subst } co = panic "substTyCo subst co"

cpSubstKiCo :: CorePrepEnv -> CoreKindCoercion -> CoreKindCoercion
cpSubstKiCo CPE{ cpe_subst = subst } co = substKiCo subst co

cpSubstMonoKi :: CorePrepEnv -> CoreMonoKind -> CoreMonoKind
cpSubstMonoKi CPE{ cpe_subst = subst } ki = substMonoKi subst ki

cpCloneBndrs :: CorePrepEnv -> [InId] -> UniqSM (CorePrepEnv, [OutId])
cpCloneBndrs env bs = mapAccumLM cpCloneBndr env bs

cpCloneLamBndrs
  :: CorePrepEnv
  -> [(InBndr, Maybe InMonoKind)]
  -> UniqSM (CorePrepEnv, [(OutBndr, Maybe OutMonoKind)])
cpCloneLamBndrs env bs = mapAccumLM cpCloneLamBndr env bs

cpCloneBndr :: CorePrepEnv -> InId -> UniqSM (CorePrepEnv, OutId)
cpCloneBndr env@CPE{ cpe_subst = subst } bndr = do
  bndr1 <- clone_it bndr
  let bndr2 = updateVarType (substTy subst) bndr1
      !unfolding' = trimUnfolding (realIdUnfolding bndr)
      bndr3 = bndr2 `setIdUnfolding` unfolding'
              `setIdSpecialization` emptyRuleInfo

  return (extendCorePrepEnv env bndr bndr3, bndr3)
  where
    clone_it bndr
      | isLocalId bndr
      = do uniq <- getUniqueM
           return (setVarUnique bndr uniq)
      | otherwise
      = return bndr

cpCloneLamBndr
  :: CorePrepEnv
  -> (InBndr, Maybe InMonoKind)
  -> UniqSM (CorePrepEnv, (OutBndr, Maybe OutMonoKind))
cpCloneLamBndr env@CPE{ cpe_subst = subst } (C.Id bndr, Just ki) = do
  bndr1 <- clone_it bndr
  let bndr2 = updateVarType (substTy subst) bndr1
      !unfolding' = trimUnfolding (realIdUnfolding bndr)
      bndr3 = bndr2 `setIdUnfolding` unfolding'
              `setIdSpecialization` emptyRuleInfo

  return (extendCorePrepEnv env bndr bndr3, (C.Id bndr3, Just (substMonoKi subst ki)))
  where
    clone_it bndr
      | isLocalId bndr
      = do uniq <- getUniqueM
           return (setVarUnique bndr uniq)
      | otherwise
      = return bndr

cpCloneLamBndr env@CPE{ cpe_subst = subst } it@(Tv bndr, Nothing) =
  if isEmptySubstTy subst
  then return (env { cpe_subst = extendTvSubstInScope subst bndr }, it)
  else let bndr1 = updateVarKind (substMonoKi subst) bndr
           subst1 = extendTvSubstWithClone subst bndr bndr1
       in return (env { cpe_subst = subst1 }, (Tv bndr1, Nothing))  

cpCloneLamBndr env@CPE{ cpe_subst = subst } it@(KCv bndr, Nothing) = do
  if isEmptySubstKiCo subst
  then return (env { cpe_subst = extendKCvSubstInScope subst bndr }, it)
  else let bndr1 = updateVarKind (substMonoKi subst) bndr
           subst1 = extendKCvSubstWithClone subst bndr bndr1
       in return (env { cpe_subst = subst1 }, (KCv bndr1, Nothing))  

cpCloneLamBndr env@CPE{ cpe_subst = subst } it@(Kv bndr, Nothing) = do
  if isEmptySubstKi subst
  then return (env { cpe_subst = extendKvSubstInScope subst bndr }, it)
  else let subst1 = extendKvSubstWithClone subst bndr bndr
       in return (env { cpe_subst = subst1 }, (Kv bndr, Nothing))  

cpCloneLamBndr _ _ = panic "cpCloneLamBndr ki mismatch"

fiddleCCall :: CoreId -> UniqSM CoreId
fiddleCCall id
  | isFCallId id = (id `setVarUnique`) <$> getUniqueM
  | otherwise = return id

newVar :: CoreType -> UniqSM CoreId
newVar ty = seqType ty `seq` mkSysLocalM (fsLit "sat") ty

wrapTicks :: Floats -> CoreExpr -> (Floats, CoreExpr)
wrapTicks floats expr
  = let (floats1, ticks1) = fold_fun go floats
    in (floats1, foldrOL mkTick expr ticks1)
  where
    fold_fun f floats = let (binds, ticks) = foldlOL f (nilOL, nilOL) (fs_binds floats)
                        in (floats { fs_binds = binds }, ticks)

    go (flt_binds, ticks) (FloatTick t)
      = assert (tickishPlace t == PlaceNonLam)
        (flt_binds, if any (flip tickishContains t) ticks
                       then ticks
                    else ticks `snocOL` t)
    go (flt_binds, ticks) f@Float{}
      = (flt_binds `snocOL` foldrOL wrap f ticks, ticks)

    wrap t (Float bind info) = Float (wrapBind t bind) info
    wrap _ f = pprPanic "Unexpected FloatingBind" (ppr f)

    wrapBind t (NonRec binder rhs) = NonRec binder (mkTick t rhs)
    wrapBind t (Rec pairs) = Rec (mapSnd (mkTick t) pairs)
