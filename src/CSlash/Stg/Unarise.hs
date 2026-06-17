{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiWayIf #-}

module CSlash.Stg.Unarise (unarise) where

import CSlash.Types.Basic
import CSlash.Core
import CSlash.Core.DataCon
import CSlash.Core.TyCon
import CSlash.Data.FastString (FastString, mkFastString, fsLit)
import CSlash.Types.Var
import CSlash.Types.Var.Id
import CSlash.Types.Literal
-- import GHC.Core.Make (aBSENT_SUM_FIELD_ERROR_ID)
import CSlash.Types.Var.Id.Make (voidPrimId, voidArgId)
import CSlash.Utils.Monad (mapAccumLM)
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Types.RepType
import CSlash.Stg.Syntax
import CSlash.Stg.Utils
import CSlash.Stg.Make
import CSlash.Core.Type
-- import GHC.Builtin.Types.Prim (intPrimTy)
import CSlash.Builtin.Types
import CSlash.Types.Unique.Supply
import CSlash.Types.Unique
import CSlash.Utils.Misc
import CSlash.Types.Var.Env

import Data.Bifunctor (second)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe (mapMaybe)
import qualified Data.IntMap as IM
import CSlash.Builtin.PrimOps
import CSlash.Builtin.PrimOps.Casts
import Data.List (mapAccumL)

{- Differences from GHC
- We only translate sums to tuples here.
- We do not need to ensure that tuples only occur in return positions.
  Because, in codegen, we treat tuples as structs.
-}

data UnariseEnv = UnariseEnv
  { ue_rho :: RhoEnv
  , ue_allow_static_conapp :: CoreDataCon -> [StgArg] -> Bool
  }

type RhoEnv = VarEnv CoreId UnariseVal

initUnariseEnv :: RhoEnv -> (CoreDataCon -> [StgArg] -> Bool) -> UnariseEnv
initUnariseEnv = UnariseEnv

data UnariseVal
  = MultiVal [OutStgArg]
  | UnaryVal OutStgArg

instance Outputable UnariseVal where
  ppr (MultiVal args) = text "MultiVal" <+> ppr args
  ppr (UnaryVal arg) = text "UnaryVal" <+> ppr arg

extendRho :: UnariseEnv -> CoreId -> UnariseVal -> UnariseEnv
extendRho env x (MultiVal args)
  = assert (all (isNvUnaryRep . stgArgRep) args)
    env { ue_rho = extendVarEnv (ue_rho env) x (MultiVal args) }
extendRho env x (UnaryVal val)
  = assert (isNvUnaryRep (stgArgRep val))
    env { ue_rho = extendVarEnv (ue_rho env) x (UnaryVal val) }

extendRhoWithoutValue :: UnariseEnv -> CoreId -> UnariseEnv
extendRhoWithoutValue env x = env { ue_rho = delVarEnv (ue_rho env) x }

lookupRho :: UnariseEnv -> CoreId -> Maybe UnariseVal
lookupRho env v = lookupVarEnv (ue_rho env) v

--------------------------------------------------------------------------------

unarise :: UniqSupply -> (CoreDataCon -> [StgArg] -> Bool) -> [StgTopBinding] -> [StgTopBinding]
unarise us is_dll_con_app binds
  = initUs_ us (mapM (unariseTopBinding (initUnariseEnv emptyVarEnv is_dll_con_app)) binds)

unariseTopBinding :: UnariseEnv -> StgTopBinding -> UniqSM StgTopBinding
unariseTopBinding rho (StgTopBind bind)
  = StgTopBind <$> unariseBinding rho True bind
unariseTopBinding _ bind@StgTopStringLit{} = return bind

unariseBinding :: UnariseEnv -> Bool -> StgBinding -> UniqSM StgBinding
unariseBinding rho top_level (StgNonRec x rhs)
  = StgNonRec x <$> unariseRhs rho top_level rhs
unariseBinding rho top_level (StgRec xrhss)
  = StgRec <$> mapM (\(x, rhs) -> (x, ) <$> unariseRhs rho top_level rhs) xrhss

unariseRhs :: UnariseEnv -> Bool -> StgRhs -> UniqSM StgRhs
unariseRhs rho top_level (StgRhsClosure ext is_join args expr ty) = do
  (rho', args1) <- unariseFunArgBinders rho args
  expr' <- unariseExpr rho' expr
  let mk_rhs = MkStgRhs
               { rhs_args = args1
               , rhs_expr = expr'
               , rhs_type = ty
               , rhs_is_join = is_join }
  if | top_level
     , Just rhs_con <- mkTopStgRhsCon_maybe (ue_allow_static_conapp rho) mk_rhs
     -> pure rhs_con
     | not top_level
     , Just rhs_con <- mkStgRhsCon_maybe mk_rhs
     -> pure rhs_con
     | otherwise
     -> pure (StgRhsClosure ext is_join args1 expr' ty)
unariseRhs rho _ (StgRhsCon con mu ts args ty)
  = assert (not (isTupleDataCon con || isSumDataCon con))
    return (StgRhsCon con mu ts (unariseConArgs rho args) ty)

--------------------------------------------------------------------------------

unariseExpr :: UnariseEnv -> StgExpr -> UniqSM StgExpr
unariseExpr rho e@(StgApp f [])
  = case lookupRho rho f of
      Just (MultiVal args) -> return (mkTuple args)
      Just (UnaryVal (StgVarArg f')) -> return (StgApp f' [])
      Just (UnaryVal (StgLitArg f')) -> return (StgLit f')
      Nothing -> return e
unariseExpr rho e@(StgApp f args)
  = return (StgApp f' (unariseFunArgs rho args))
  where
    f' = case lookupRho rho f of
           Just (UnaryVal (StgVarArg f')) -> f'
           Nothing -> f
           err -> pprPanic "unariseExpr - app2" (pprStgExpr panicStgPprOpts e $$ ppr err)
unariseExpr _ (StgLit l) = return (StgLit l)
unariseExpr rho (StgConApp dc n args ty_args)
  | isSumDataCon dc || isTupleDataCon dc
  = do us <- getUniqueSupplyM
       case unariseSumOrTupleArgs rho us dc args ty_args of
         (args', Just cast_wrapper) -> return $ cast_wrapper (mkTuple args')
         (args', Nothing) -> return (mkTuple args')
  | otherwise
  = let args' = unariseConArgs rho args
    in return (StgConApp dc n args' [])
unariseExpr rho (StgOpApp op args ty)
  = return (StgOpApp op (unariseFunArgs rho args) ty)
unariseExpr rho (StgCase scrut bndr alt_ty alts)
  | StgApp v [] <- scrut
  , Just (MultiVal xs) <- lookupRho rho v
  = elimCase rho xs bndr alt_ty alts
  | StgConApp dc _ args ty_args <- scrut
  , isSumDataCon dc || isTupleDataCon dc
  = do us <- getUniqueSupplyM
       case unariseSumOrTupleArgs rho us dc args ty_args of
         (args', Just wrapper) -> wrapper <$> elimCase rho args' bndr alt_ty alts
         (args', Nothing) -> elimCase rho args' bndr alt_ty alts
  | StgLit lit <- scrut
  , Just args' <- unariseLiteral_maybe lit
  = elimCase rho args' bndr alt_ty alts
  | otherwise
  = do scrut' <- unariseExpr rho scrut
       alts' <- unariseAlts rho alt_ty bndr alts
       return (StgCase scrut' bndr alt_ty alts')
unariseExpr rho (StgLet ext bind e)
  = StgLet ext <$> unariseBinding rho False bind <*> unariseExpr rho e
unariseExpr rho (StgLetNoEscape ext bind e)
  = StgLetNoEscape ext <$> unariseBinding rho False bind <*> unariseExpr rho e
unariseExpr rho (StgTick tick e)
  = StgTick tick <$> unariseExpr rho e

unariseSumOrTupleArgs
  :: UnariseEnv
  -> UniqSupply
  -> CoreDataCon
  -> [InStgArg]
  -> [[PrimRep]]
  -> ([OutStgArg], Maybe (StgExpr -> StgExpr))
unariseSumOrTupleArgs rho us dc args ty_args
  | isTupleDataCon dc
  = (unariseConArgs rho args, Nothing)
  | isSumDataCon dc
  = let args1 = assert (isSingleton args) (unariseConArgs rho args)
        (args2, cast_wrapper) = mkSum dc ty_args args1 us
    in (args2, Just cast_wrapper)
  | otherwise
  = panic "unariseSumOrTupleArgs: Constructor not a sum or tuple"

unariseLiteral_maybe :: Literal -> Maybe [OutStgArg]
unariseLiteral_maybe = panic "unariseLiteral_maybe"
  
--------------------------------------------------------------------------------

elimCase
  :: UnariseEnv
  -> [OutStgArg]
  -> InId
  -> AltType
  -> [InStgAlt]
  -> UniqSM OutStgExpr
elimCase rho args bndr (MultiValAlt _) [GenStgAlt{ alt_bndrs = bndrs, alt_rhs = rhs }]
  = do let rho1 = extendRho rho bndr (MultiVal args)
       (rho2, rhs') <- if isTupleBndr bndr
                       then return (mapTupleIdBinders bndrs args rho1, rhs)
                       else assert (isSumBndr bndr) $
                            case bndrs of
                              [] -> return (rho1, rhs)
                              [alt_bndr] -> mapSumIdBinders alt_bndr args rhs rho1
                              _ -> pprPanic "mapSumIdBinders" (ppr bndrs $$ ppr args)
       unariseExpr rho2 rhs'
       
elimCase rho args@(tag_arg : real_args) bndr (MultiValAlt _) alts
  | isSumBndr bndr
  = do tag_bndr <- mkId (mkFastString "tag") tagTy
       let rho1 = extendRho rho bndr (MultiVal args)
           scrut' = case tag_arg of
                      StgVarArg v -> StgApp v []
                      StgLitArg l -> StgLit l
       alts' <- unariseSumAlts rho1 real_args alts
       return (StgCase scrut' tag_bndr tagAltTy alts')

elimCase _ args bndr alt_ty alts
  = pprPanic "elimCase - unhandled case"
    (ppr args <+> ppr bndr <+> ppr alt_ty $$ pprPanicAlts alts)

--------------------------------------------------------------------------------

unariseAlts :: UnariseEnv -> AltType -> InId -> [StgAlt] -> UniqSM [StgAlt]
unariseAlts rho (MultiValAlt n) bndr [GenStgAlt{ alt_con = DEFAULT, alt_bndrs = [], alt_rhs = e }]
  | isTupleBndr bndr
  = do (rho', ys) <- unariseConArgBinder rho bndr
       !e' <- unariseExpr rho' e
       return [GenStgAlt (DataAlt (tupleDataCon n)) ys e']
unariseAlts rho (MultiValAlt n) bndr [GenStgAlt{alt_con = DataAlt _, alt_bndrs = ys, alt_rhs = e}]
  | isTupleBndr bndr
  = do (rho', ys1) <- unariseConArgBinders rho ys
       massert (ys1 `lengthIs` n)
       let rho'' = extendRho rho' bndr (MultiVal (map StgVarArg ys1))
       !e' <- unariseExpr rho'' e
       return [GenStgAlt (DataAlt (tupleDataCon n)) ys1 e']
unariseAlts _ (MultiValAlt _) bndr alts
  | isTupleBndr bndr
  = pprPanic "unariseExpr: strange multi val alts" (pprPanicAlts alts)

unariseAlts rho (MultiValAlt _) bndr [GenStgAlt{ alt_con = DEFAULT, alt_bndrs = [], alt_rhs = rhs }]
  | isSumBndr bndr
  = do (rho_sum_bndrs, sum_bndrs) <- unariseConArgBinder rho bndr
       rhs' <- unariseExpr rho_sum_bndrs rhs
       return [GenStgAlt (DataAlt (tupleDataCon (length sum_bndrs))) sum_bndrs rhs']

unariseAlts rho (MultiValAlt _) bndr alts
  | isSumBndr bndr
  = do (rho_sum_bndrs, scrut_bndrs@(tag_bndr : real_bndrs)) <- unariseConArgBinder rho bndr
       alts' <- unariseSumAlts rho_sum_bndrs (map StgVarArg real_bndrs) alts
       let inner_case = StgCase (StgApp tag_bndr []) tag_bndr tagAltTy alts'
       return [GenStgAlt{ alt_con = DataAlt (tupleDataCon (length scrut_bndrs))
                        , alt_bndrs = scrut_bndrs
                        , alt_rhs = inner_case }]

unariseAlts rho _ _ alts = mapM (\alt -> unariseAlt rho alt) alts

unariseAlt :: UnariseEnv -> StgAlt -> UniqSM StgAlt
unariseAlt rho alt@GenStgAlt{ alt_bndrs = xs, alt_rhs = e } = do
  (rho', xs') <- unariseConArgBinders rho xs
  !e' <- unariseExpr rho' e
  return $! alt { alt_bndrs = xs', alt_rhs = e' }

--------------------------------------------------------------------------------

unariseSumAlts :: UnariseEnv -> [StgArg] -> [StgAlt] -> UniqSM [StgAlt]
unariseSumAlts env args alts = do
  alts' <- mapM (unariseSumAlt env args) alts
  return (mkDefaultLitAlt alts')

unariseSumAlt :: UnariseEnv -> [StgArg] -> StgAlt -> UniqSM StgAlt
unariseSumAlt rho _ GenStgAlt{ alt_con = DEFAULT, alt_rhs = e }
  = GenStgAlt DEFAULT mempty <$> unariseExpr rho e
unariseSumAlt rho args alt@GenStgAlt{ alt_con = DataAlt sumCon, alt_bndrs = bs, alt_rhs = e } = do
  (rho', e') <- case bs of
                  [b] -> mapSumIdBinders b args e rho
                  _ -> pprPanic "unariseSumAlt2" (ppr args $$ pprPanicAlt alt)
  let lit_case = LitAlt (LitNumber (LitNumInt 64) (fromIntegral (dataConTag sumCon))) -- TODO: sum tag size?
  GenStgAlt lit_case mempty <$> unariseExpr rho' e'
unariseSumAlt _ scrut alt = pprPanic "unariiseSumAlt3" (ppr scrut $$ pprPanicAlt alt)

--------------------------------------------------------------------------------

mapTupleIdBinders :: [InId] -> [OutStgArg] -> UnariseEnv -> UnariseEnv
mapTupleIdBinders ids args0 rho0
  = assert (not (any (null . stgArgRep) args0)) $
    let map_ids :: UnariseEnv -> [CoreId] -> [StgArg] -> UnariseEnv
        map_ids rho [] _ = rho
        map_ids rho (x:xs) args =
          let x_reps = typePrimRep (varType x)
              x_arity = length x_reps
              (x_args, args') = assert (args `lengthAtLeast` x_arity) splitAt x_arity args
              rho' | x_arity == 1
                   = assert (x_args `lengthIs` 1)
                     extendRho rho x (UnaryVal (head x_args))
                   | otherwise
                   = extendRho rho x (MultiVal x_args)
          in map_ids rho' xs args'
    in map_ids rho0 ids args0

mapSumIdBinders
  :: InId
  -> [OutStgArg]
  -> InStgExpr
  -> UnariseEnv
  -> UniqSM (UnariseEnv, OutStgExpr)
mapSumIdBinders alt_bndr args rhs rho0
  = assert (not (any (null . stgArgRep) args)) $ do
    uss <- listSplitUniqSupply <$> getUniqueSupplyM
    let fld_reps = typePrimRep (varType alt_bndr)
        arg_slots = map primRepSlot $ concatMap stgArgRep args
        id_slots = map primRepSlot fld_reps
        layout1 = layoutSum arg_slots id_slots

        id_arg_exprs = [args !! i | i <- layout1 ]
        id_vars = [v | StgVarArg v <- id_arg_exprs]

        typed_id_arg_input = assert (equalLength id_vars fld_reps) $
                             zip3 id_vars fld_reps uss

        mkCastInput
          :: (CoreId, PrimRep, UniqSupply)
          -> ([(PrimOp, CoreType, Unique)], CoreId, CoreId)
        mkCastInput (id, rep, bndr_us) =
          let (ops, types) = unzip $ getCasts (typePrimRepU $ varType id) rep
              cst_opts = zip3 ops types $ uniqsFromSupply bndr_us
              out_id = case cst_opts of
                         [] -> id
                         _ -> let (_, ty, uq) = last cst_opts in mkCastVar uq ty
          in (cst_opts, id, out_id)

        cast_inputs = map mkCastInput typed_id_arg_input
        (rhs_with_casts, typed_ids) = mapAccumL cast_arg (\x -> x) cast_inputs
          where cast_arg rhs_in (cast_ops, in_id, out_id)
                  = let rhs_out = castArgRename cast_ops (StgVarArg in_id)
                    in (rhs_in . rhs_out, out_id)

        typed_id_args = map StgVarArg typed_ids

    if isMultiValBndr alt_bndr
       then return (extendRho rho0 alt_bndr (MultiVal typed_id_args), rhs_with_casts rhs)
      else assert (typed_id_args `lengthIs` 1) $
           return (extendRho rho0 alt_bndr (UnaryVal (head typed_id_args)), rhs_with_casts rhs)

castArgRename :: [(PrimOp, CoreType, Unique)] -> StgArg -> StgExpr -> StgExpr
castArgRename ops in_arg rhs = case ops of
  [] -> rhs
  ((op, ty, uq) : rest_ops) ->
    let out_id' = mkCastVar uq ty
        sub_cast = castArgRename rest_ops (StgVarArg out_id')
    in mkCast in_arg op out_id' ty $ sub_cast rhs

mkCastVar :: Unique -> CoreType -> CoreId
mkCastVar uq ty = mkSysLocal (fsLit "cst_sum") uq ty

mkCast :: StgArg -> PrimOp -> OutId -> CoreType -> StgExpr -> StgExpr
mkCast arg_in cast_op out_id out_ty in_rhs =
  let r2 = typePrimRepU out_ty
      scrut = StgOpApp (StgPrimOp cast_op) [arg_in] out_ty
      alt = GenStgAlt { alt_con = DEFAULT, alt_bndrs = [], alt_rhs = in_rhs }
      alt_ty = PrimAlt r2
  in (StgCase scrut out_id alt_ty [alt])

mkSum
  :: HasDebugCallStack
  => CoreDataCon
  -> [[PrimRep]]
  -> [OutStgArg]
  -> UniqSupply
  -> ([OutStgArg], StgExpr -> StgExpr)
mkSum dc ty_args args0 us
  = let _ :| sum_slots = sumRepType ty_args -- drop tag slot
        field_slots = mapMaybe (repSlotTy . stgArgRep) args0
        tag = dataConTag dc
        layout' = layoutSum sum_slots field_slots

        tag_arg = StgLitArg (LitNumber (LitNumInt 64) (fromIntegral tag)) -- TODO: sum tag size?
        arg_idxs = IM.fromList (zipEqual "mkSum" layout' args0)

        ((_, _, _, wrapper), slot_args)
          = assert (length arg_idxs <= length sum_slots) $
            mapAccumL mkTupArg (0, arg_idxs, us, id) sum_slots

        mkTupArg
          :: (Int, IM.IntMap StgArg, UniqSupply, StgExpr -> StgExpr)
          -> SlotTy
          -> ((Int, IM.IntMap StgArg, UniqSupply, StgExpr -> StgExpr), StgArg)
        mkTupArg (arg_idx, arg_map, us, wrapper) slot
          | Just stg_arg <- IM.lookup arg_idx arg_map
          = case castArg us slot stg_arg of
              Just (casted_arg, us', wrapper') ->
                ((arg_idx + 1, arg_map, us', wrapper . wrapper'), casted_arg)
              Nothing -> ((arg_idx + 1, arg_map, us, wrapper), stg_arg)
          | otherwise
          = ((arg_idx + 1, arg_map, us, wrapper), sumRubbishArg slot)

        castArg
          :: UniqSupply
          -> SlotTy
          -> StgArg
          -> Maybe (StgArg, UniqSupply, StgExpr -> StgExpr)
        castArg us slot_ty arg
          | slotPrimRep slot_ty /= stgArgRepU arg
          , (ops, types) <- unzip $ getCasts (stgArgRepU arg) $ slotPrimRep slot_ty
          , not . null $ ops
          = let (us1, us2) = splitUniqSupply us
                cast_uqs = uniqsFromSupply us1
                cast_opts = zip3 ops types cast_uqs
                (_, out_ty, out_uq) = last cast_opts
                casts = castArgRename cast_opts arg
            in Just (StgVarArg (mkCastVar out_uq out_ty), us2, casts)
          | otherwise
          = Nothing

        tup_args = tag_arg : slot_args

    in (tup_args, wrapper)

sumRubbishArg :: SlotTy -> StgArg
sumRubbishArg (WordSlot i) = StgLitArg (LitNumber (LitNumWord i) 0)
sumRubbishArg FloatSlot = StgLitArg (LitFloat 0)
sumRubbishArg DoubleSlot = StgLitArg (LitDouble 0)

--------------------------------------------------------------------------------

unariseArgBinder :: Bool -> UnariseEnv -> CoreId -> UniqSM (UnariseEnv, [CoreId])
unariseArgBinder is_con_arg rho x
  = case typePrimRep (varType x) of
      [] | is_con_arg
           -> return (extendRho rho x (MultiVal []), [])
         | otherwise
           -> return (extendRho rho x (MultiVal[]), [voidArgId])
      [rep]
        | isSumType (varType x) || isTupleType (varType x)
          -> do x' <- mkId (mkFastString "us") (primRepToType rep)
                return (extendRho rho x (MultiVal [StgVarArg x']), [x'])
        | otherwise
          -> return (extendRhoWithoutValue rho x, [x])

      reps -> do
        xs <- mkIds (mkFastString "us") (map primRepToType reps)
        return (extendRho rho x (MultiVal (map StgVarArg xs)), xs)

--------------------------------------------------------------------------------

unariseFunArg :: UnariseEnv -> StgArg -> [StgArg]
unariseFunArg rho (StgVarArg x) =
  case lookupRho rho x of
    Just (MultiVal []) -> [voidArg]
    Just (MultiVal as) -> as
    Just (UnaryVal arg) -> [arg]
    Nothing -> [StgVarArg x]
unariseFunArg _ arg@(StgLitArg lit) = case unariseLiteral_maybe lit of
  Just [] -> [voidArg]
  Just as -> as
  Nothing -> [arg]

unariseFunArgs :: UnariseEnv -> [StgArg] -> [StgArg]
unariseFunArgs = concatMap . unariseFunArg

unariseFunArgBinders :: UnariseEnv -> [CoreId] -> UniqSM (UnariseEnv, [CoreId])
unariseFunArgBinders rho xs = second concat <$> mapAccumLM unariseFunArgBinder rho xs

unariseFunArgBinder :: UnariseEnv -> CoreId -> UniqSM (UnariseEnv, [CoreId])
unariseFunArgBinder = unariseArgBinder False

--------------------------------------------------------------------------------

unariseConArg :: UnariseEnv -> InStgArg -> [OutStgArg]
unariseConArg rho (StgVarArg x) =
  case lookupRho rho x of
    Just (UnaryVal arg) -> [arg]
    Just (MultiVal as) -> as
    Nothing
      | isZeroBitTy (varType x) -> []
      | otherwise -> [StgVarArg x]
unariseConArg _ arg@(StgLitArg lit)
  | Just as <- unariseLiteral_maybe lit
  = as
  | otherwise
  = assert (isNvUnaryRep (typePrimRep (literalType lit)))
    [arg]

unariseConArgs :: UnariseEnv -> [InStgArg] -> [OutStgArg]
unariseConArgs = concatMap . unariseConArg

unariseConArgBinders :: UnariseEnv -> [CoreId] -> UniqSM (UnariseEnv, [CoreId])
unariseConArgBinders rho xs = second concat <$> mapAccumLM unariseConArgBinder rho xs

unariseConArgBinder :: UnariseEnv -> CoreId -> UniqSM (UnariseEnv, [CoreId])
unariseConArgBinder = unariseArgBinder True

--------------------------------------------------------------------------------

mkIds :: FastString -> [NvUnaryType] -> UniqSM [CoreId]
mkIds fs tys = mkUnarisedIds fs tys

mkId :: FastString -> NvUnaryType -> UniqSM CoreId
mkId s t = mkUnarisedId s t

isMultiValBndr :: CoreId -> Bool
isMultiValBndr id
  | [_] <- typePrimRep (varType id)
  = False
  | otherwise
  = True

isSumBndr :: CoreId -> Bool
isSumBndr = isSumType . varType

isTupleBndr :: CoreId -> Bool
isTupleBndr = isTupleType . varType

mkTuple :: [StgArg] -> StgExpr
mkTuple args = StgConApp (tupleDataCon (length args)) NoNumber args []

tagAltTy :: AltType
tagAltTy = PrimAlt (IntRep 64) -- TODO: tag size?

tagTy :: CoreType 
tagTy = panic "tagTy"

voidArg :: StgArg
voidArg = StgVarArg voidPrimId

mkDefaultLitAlt :: [StgAlt] -> [StgAlt]
mkDefaultLitAlt [] = pprPanic "elimSumExpr.mkDefaultAlt" (text "Empty alts")
mkDefaultLitAlt alts@(GenStgAlt{ alt_con = DEFAULT } : _) = alts
mkDefaultLitAlt (alt@GenStgAlt{ alt_con = LitAlt{}, alt_bndrs = [] } : alts)
  = alt { alt_con = DEFAULT } : alts
mkDefaultLitAlt alts = pprPanic "mkDefaultLitAlt" (text "Not a lit alts:" <+> pprPanicAlts alts)

pprPanicAlts :: OutputablePass pass => [GenStgAlt pass] -> SDoc
pprPanicAlts alts = ppr (map pprPanicAlt alts)

pprPanicAlt :: OutputablePass pass => GenStgAlt pass -> SDoc
pprPanicAlt GenStgAlt{ alt_con = c, alt_bndrs = b, alt_rhs = e }
  = ppr (c, b, pprStgExpr panicStgPprOpts e)
