module CSlash.Core.Opt.FloatOut (floatOutwards) where

import CSlash.Core
import CSlash.Core.Utils
import CSlash.Core.Make
-- import GHC.Core.Opt.Arity ( exprArity, etaExpand )
import CSlash.Core.Opt.Monad ( FloatOutSwitches(..) )

import CSlash.Driver.Flags  ( DumpFlag (..) )
import CSlash.Utils.Logger
import CSlash.Types.Var.Id
import CSlash.Types.Tickish
import CSlash.Core.Opt.SetLevels
import CSlash.Types.Unique.Supply ( UniqSupply )
import CSlash.Data.Bag
import CSlash.Utils.Misc
import CSlash.Data.Maybe
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Core.Type
import qualified Data.IntMap as M

import Data.List        ( partition )

{- *********************************************************************
*                                                                      *
                  floatOutwards
*                                                                      *
********************************************************************* -}

floatOutwards
  :: Logger
  -> FloatOutSwitches
  -> UniqSupply
  -> CoreProgram -> IO CoreProgram
floatOutwards logger float_sws us pgm = do
  let annotated_w_levels = setLevels float_sws pgm us
      (fss, binds_s') = unzip (map floatTopBind annotated_w_levels)

  putDumpFileMaybe logger Opt_D_verbose_core2core "Levels added:"
    FormatCore
    (vcat (map ppr annotated_w_levels))

  let (tlets, ntlets, lams) = get_stats (sum_stats fss)

  putDumpFileMaybe logger Opt_D_dump_simpl_stats "FloatOut stats:"
    FormatText
    (hcat [ int tlets, text " Lets floated to top level; "
          , int ntlets, text " Lets floated elsewhere; from "
          , int lams, text " Lambda group" ])

  return (bagToList (unionManyBags binds_s'))

floatTopBind :: LevelledBind -> (FloatStats, Bag CoreBind)
floatTopBind bind = case floatBind bind of
  (fs, floats, bind') -> let float_bag = flattenTopFloats floats
                         in case bind' of
                              [Rec prs] -> (fs, unitBag (Rec (addTopFloatPairs float_bag prs)))
                              [NonRec b e] -> (fs, float_bag `snocBag` NonRec b e)
                              _ -> pprPanic "floatTopBind" (ppr bind')

{- *********************************************************************
*                                                                      *
                  Floating in a binding (the business end)
*                                                                      *
********************************************************************* -}

floatBind :: LevelledBind -> (FloatStats, FloatBinds, [CoreBind])
floatBind (NonRec (TB var _) rhs)
  = case floatRhs var rhs of
      (fs, rhs_floats, rhs') -> (fs, rhs_floats, [NonRec var rhs'])
floatBind (Rec pairs)
  = case floatList do_pair pairs of
      (fs, rhs_floats, new_pairs) ->
        let (new_ul_pairss, new_other_pairss) = unzip new_pairs
            (new_join_pairs, new_l_pairs) = partition (isJoinId . fst) (concat new_other_pairss)

            new_rec_binds | null new_join_pairs = [ Rec new_l_pairs ]
                          | null new_l_pairs = [ Rec new_join_pairs ]
                          | otherwise = [ Rec new_l_pairs
                                        , Rec new_join_pairs ]

            new_non_rec_binds = [ NonRec b e | (b, e) <- concat new_ul_pairss ]
        in (fs, rhs_floats, new_non_rec_binds ++ new_rec_binds)
  where
    do_pair
      :: (LevelledLetBndr, LevelledExpr)
      -> (FloatStats, FloatBinds, ([(CoreId, CoreExpr)], [(CoreId, CoreExpr)]))
    do_pair (TB name spec, rhs)
      | isTopLvl dest_lvl
      = case floatRhs name rhs of
          (fs, rhs_floats, rhs')
            -> ( fs
               , emptyFloats
               , ([], addTopFloatPairs (flattenTopFloats rhs_floats) [(name, rhs')]))

      | otherwise
      = case floatRhs name rhs of
          (fs, rhs_floats, rhs')
            -> case partitionByLevel dest_lvl rhs_floats of
                 (rhs_floats', heres)
                   -> case splitRecFloats heres of
                        (ul_pairs, pairs, case_heres)
                          -> let pairs' = (name, installUnderLambdas case_heres rhs') : pairs
                             in (fs, rhs_floats', (ul_pairs, pairs'))
      where dest_lvl = floatSpecLevel spec

splitRecFloats
  :: Bag FloatBind
  -> ([(CoreId, CoreExpr)], [(CoreId, CoreExpr)], Bag FloatBind)
splitRecFloats fs = go [] [] (bagToList fs)
  where
    go ul_prs prs (FloatLet (NonRec b r) : fs)
      | not (isJoinId b)
      = go ((b, r) : ul_prs) prs fs
      | otherwise
      = go ul_prs ((b, r) : prs) fs
    go ul_prs prs (FloatLet (Rec prs') : fs) = go ul_prs (prs' ++ prs) fs
    go ul_prs prs fs = (reverse ul_prs, prs, listToBag fs)

installUnderLambdas :: Bag FloatBind -> CoreExpr -> CoreExpr
installUnderLambdas floats e
  | isEmptyBag floats = e
  | otherwise = go e
  where
    go (Lam b k e) = Lam b k (go e)
    go e = install floats e

floatList :: (a -> (FloatStats, FloatBinds, b)) -> [a] -> (FloatStats, FloatBinds, [b])
floatList _ [] = (zeroStats, emptyFloats, [])
floatList f (a:as) = case f a of
  (fs_a, binds_a, b)
    -> case floatList f as of
         (fs_as, binds_as, bs)
           -> (fs_a `add_stats` fs_as, binds_a `plusFloats` binds_as, b:bs)

{- *********************************************************************
*                                                                      *
                  Floating in expressions
*                                                                      *
********************************************************************* -}

floatBody
  :: Level
  -> LevelledExpr
  -> (FloatStats, FloatBinds, CoreExpr)
floatBody lvl arg
  = case floatExpr arg of
      (fsa, floats, arg') ->
        case partitionByLevel lvl floats of
          (floats', heres) -> (fsa, floats', install heres arg')

floatExpr :: LevelledExpr -> (FloatStats, FloatBinds, CoreExpr)
floatExpr (Var v) = (zeroStats, emptyFloats, Var v)
floatExpr (Type ty) = (zeroStats, emptyFloats, Type ty)
floatExpr (KiCo co) = (zeroStats, emptyFloats, KiCo co)
floatExpr (Kind ki) = (zeroStats, emptyFloats, Kind ki)
floatExpr (Lit lit) = (zeroStats, emptyFloats, Lit lit)

floatExpr (App e a)
  = case floatExpr e of
      (fse, floats_e, e') ->
        case floatExpr a of
          (fsa, floats_a, a') ->
            (fse `add_stats` fsa, floats_e `plusFloats` floats_a, App e' a')
floatExpr lam@(Lam (TB _ lam_spec) _ _)
  = let (bndrs_w_lvls, body) = collectBinders lam
        bndrs = [(b, mki) | (TB b _, mki) <- bndrs_w_lvls]
        bndr_lvl = floatSpecLevel lam_spec
    in case floatBody bndr_lvl body of
         (fs, floats, body') -> (add_to_stats fs floats, floats, mkCoreLams bndrs body')

floatExpr (Tick tickish expr) = panic "floatExpr Tick"

floatExpr (Cast expr co)
  = case floatExpr expr of
      (fs, floating_defns, expr') -> (fs, floating_defns, Cast expr' co)

floatExpr (Let bind body)
  = case bind_spec of
      FloatMe dest_lvl
        -> case (floatBind bind) of
             (fsb, bind_floats, binds')
               -> case (floatExpr body) of
                    (fse, body_floats, body') ->
                      let new_bind_floats = foldr plusFloats emptyFloats
                                            (map (unitLetFloat dest_lvl) binds')
                      in ( add_stats fsb fse
                         , bind_floats `plusFloats` new_bind_floats
                           `plusFloats` body_floats
                         , body' )
      StayPut bind_lvl
        -> case floatBind bind of
             (fsb, bind_floats, binds')
               -> case floatBody bind_lvl body of
                    (fse, body_floats, body')
                      -> ( add_stats fsb fse
                         , bind_floats `plusFloats` body_floats
                         , foldr Let body' binds' )
  where
    bind_spec = case bind of
                  NonRec (TB _ s) _ -> s
                  Rec ((TB _ s, _) : _) -> s
                  Rec [] -> panic "floatExpr:rec"

floatExpr (Case scrut (TB case_bndr case_spec) ty alts)
  = case case_spec of
      FloatMe dest_lvl
        | [Alt con@(DataAlt {}) bndrs rhs] <- alts
        -> case floatExpr scrut of
             (fse, fde, scrut')
               -> case floatExpr rhs of
                    (fsb, fdb, rhs') ->
                      let float = unitCaseFloat dest_lvl scrut'
                                  case_bndr con [b | TB b _ <- bndrs]
                      in (add_stats fse fsb, fde `plusFloats` float `plusFloats` fdb, rhs')
        | otherwise -> pprPanic "Floating multi-case" (ppr alts)

      StayPut bind_lvl
        -> case floatExpr scrut of
             (fse, fde, scrut')
               -> case floatList (float_alt bind_lvl) alts of
                    (fsa, fda, alts') ->
                      (add_stats fse fsa, fda `plusFloats` fde, Case scrut' case_bndr ty alts')
  where
    float_alt bind_lvl (Alt con bs rhs)
      = case floatBody bind_lvl rhs of
          (fs, rhs_floats, rhs') -> (fs, rhs_floats, Alt con [b | TB b _ <- bs] rhs')

floatRhs
  :: CoreId
  -> LevelledExpr
  -> (FloatStats, FloatBinds, CoreExpr)
floatRhs bndr rhs
  | JoinPoint join_arity <- idJoinPointHood bndr
  , Just (bndrs, body) <- try_collect join_arity rhs []
  = case bndrs of
      [] -> floatExpr rhs
      (TB _ lam_spec, _) : _ ->
        let lvl = floatSpecLevel lam_spec
        in case floatBody lvl body of
             (fs, floats, body') -> (fs, floats
                                    , mkCoreLams [(b, mki) | (TB b _, mki) <- bndrs] body')
  | otherwise
  = floatExpr rhs
  where
    try_collect 0 expr acc = Just (reverse acc, expr)
    try_collect n (Lam b mki e) acc = try_collect (n - 1) e ((b, mki) : acc)
    try_collect _ _ _ = Nothing

{- *********************************************************************
*                                                                      *
             Utility bits for floating stats
*                                                                      *
********************************************************************* -}

data FloatStats = FlS Int Int Int

get_stats :: FloatStats -> (Int, Int, Int)
get_stats (FlS a b c) = (a, b, c)

zeroStats :: FloatStats
zeroStats = FlS 0 0 0

sum_stats :: [FloatStats] -> FloatStats
sum_stats  xs = foldr add_stats zeroStats xs

add_stats :: FloatStats -> FloatStats -> FloatStats
add_stats (FlS a1 b1 c1) (FlS a2 b2 c2)
  = FlS (a1 + a2) (b1 + b2) (c1 + c2)

add_to_stats :: FloatStats -> FloatBinds -> FloatStats
add_to_stats (FlS a b c) (FB tops others)
  = FlS (a + lengthBag tops)
        (b + lengthBag (flattenMajor others))
        (c + 1)

{- *********************************************************************
*                                                                      *
             Utility bits for floating 
*                                                                      *
********************************************************************* -}

type FloatLet = CoreBind
type MajorEnv = M.IntMap MinorEnv
type MinorEnv = M.IntMap (Bag FloatBind)

data FloatBinds = FB !(Bag FloatLet) !MajorEnv

instance Outputable FloatBinds where
  ppr (FB fbs defs) = text "FB" <+> (braces $ vcat
                                     [ text "tops =" <+> ppr fbs
                                     , text "non-tops =" <+> ppr defs ])

flattenTopFloats :: FloatBinds -> Bag CoreBind
flattenTopFloats (FB tops defs)
  = assertPpr (isEmptyBag (flattenMajor defs)) (ppr defs) $ tops

addTopFloatPairs :: Bag CoreBind -> [(CoreId, CoreExpr)] -> [(CoreId, CoreExpr)]
addTopFloatPairs float_bag prs
  = foldr add prs float_bag
  where
    add (NonRec b r) prs = (b, r) : prs
    add (Rec prs1) prs2 = prs1 ++ prs2

flattenMajor :: MajorEnv -> Bag FloatBind
flattenMajor = M.foldr (unionBags . flattenMinor) emptyBag

flattenMinor :: MinorEnv -> Bag FloatBind
flattenMinor = M.foldr unionBags emptyBag

emptyFloats :: FloatBinds
emptyFloats  = FB emptyBag M.empty

unitCaseFloat :: Level -> CoreExpr -> CoreId -> AltCon -> [CoreId] -> FloatBinds
unitCaseFloat (Level major minor) e b con bs
  = FB emptyBag (M.singleton major (M.singleton minor floats))
  where
    floats = unitBag (FloatCase e b con bs)

unitLetFloat :: Level -> FloatLet -> FloatBinds
unitLetFloat lvl@(Level major minor) b
  | isTopLvl lvl = FB (unitBag b) M.empty
  | otherwise = FB emptyBag (M.singleton major (M.singleton minor floats))
  where
    floats = unitBag (FloatLet b)

plusFloats :: FloatBinds -> FloatBinds -> FloatBinds
plusFloats (FB t1 l1) (FB t2 l2)
  = FB (t1 `unionBags` t2) (l1 `plusMajor` l2)

plusMajor :: MajorEnv -> MajorEnv -> MajorEnv
plusMajor = M.unionWith plusMinor

plusMinor :: MinorEnv -> MinorEnv -> MinorEnv
plusMinor = M.unionWith unionBags

install :: Bag FloatBind -> CoreExpr -> CoreExpr
install defn_groups expr = foldr wrapFloat expr defn_groups

partitionByLevel
  :: Level
  -> FloatBinds
  -> (FloatBinds, Bag FloatBind)
partitionByLevel (Level major minor) (FB tops defns)
  = ( FB tops (outer_maj `plusMajor` M.singleton major outer_min)
    , here_min `unionBags` flattenMinor inner_min
      `unionBags` flattenMajor inner_maj )
  where
    (outer_maj, mb_here_maj, inner_maj) = M.splitLookup major defns
    (outer_min, mb_here_min, inner_min) = case mb_here_maj of
                                            Nothing -> (M.empty, Nothing, M.empty)
                                            Just min_defns -> M.splitLookup minor min_defns
    here_min = mb_here_min `orElse` emptyBag
