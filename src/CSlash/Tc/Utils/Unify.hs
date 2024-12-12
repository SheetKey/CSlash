module CSlash.Tc.Utils.Unify where

import CSlash.Cs

-- import GHC.Tc.Utils.Concrete ( hasFixedRuntimeRep, hasFixedRuntimeRep_syntactic )
import CSlash.Tc.Utils.Env
-- import GHC.Tc.Utils.Instantiate
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Utils.TcMType
import CSlash.Tc.Utils.TcType
-- import GHC.Tc.Types.Evidence
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Origin
import CSlash.Tc.Zonk.TcType

import CSlash.Core.Type
import CSlash.Core.Type.Rep
-- import GHC.Core.TyCo.FVs( isInjectiveInType )
-- import CSlash.Core.Type.Ppr( debugPprType {- pprTyVar -} )
import CSlash.Core.TyCon
-- import GHC.Core.Coercion
import CSlash.Core.Kind
import CSlash.Core.Kind.Compare (tcEqKind)
-- import GHC.Core.Reduction

import CSlash.Builtin.Types
import CSlash.Types.Name
-- import CSlash.Types.Id( idType )
import CSlash.Types.Var as Var
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Types.Basic
import CSlash.Types.Unique.Set (nonDetEltsUniqSet)

import CSlash.Utils.Error
import CSlash.Utils.Misc
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic

import CSlash.Driver.DynFlags
import CSlash.Data.Bag
import CSlash.Data.FastString( fsLit )

import Control.Monad
import Data.Monoid as DM ( Any(..) )
import qualified Data.Semigroup as S ( (<>) )

{- *********************************************************************
*                                                                      *
          Skolemisation and matchExpectedFunTys
*                                                                      *
********************************************************************* -}

emitResidualTvConstraint :: SkolemInfo -> [TcTyVar] -> TcLevel -> WantedConstraints -> TcM ()
emitResidualTvConstraint skol_info skol_tvs tclvl wanted
  | not (isEmptyWC wanted)
    || checkTelescopeSkol (getSkolemInfo skol_info)
  = do implic <- buildTvImplication (getSkolemInfo skol_info) skol_tvs tclvl wanted
       emitImplication implic
  | otherwise
  = return ()

buildTvImplication
  :: SkolemInfoAnon
  -> [TcTyVar]
  -> TcLevel
  -> WantedConstraints
  -> TcM Implication
buildTvImplication skol_info skol_tvs tclvl wanted
  = assertPpr (all (isSkolemTyVar <||> isTyVarTyVar) skol_tvs) (ppr skol_tvs) $ do
      implic <- newImplication
      let implic' = implic { ic_tclvl = tclvl
                           , ic_skols = skol_tvs
                           , ic_given_eqs = NoGivenEqs
                           , ic_wanted = wanted
                           , ic_info = skol_info }
      checkImplicationInvariants implic'
      return implic'

{- *********************************************************************
*                                                                      *
                Unification
*                                                                      *
********************************************************************* -}

unifyKindAndEmit :: CtOrigin -> TcKind -> TcKind -> TcM ()
unifyKindAndEmit orig ki1 ki2 = do
  ref <- newTcRef emptyBag
  loc <- getCtLocM orig
  let env = UE { u_loc = loc
               , u_defer = ref
               , u_unified = Nothing }
  uKind env ki1 ki2
  cts <- readTcRef ref
  unless (null cts) (emitSimples cts)

{- *********************************************************************
*                                                                      *
                uType and uKind
*                                                                      *
********************************************************************* -}

data UnifyEnv = UE
  { u_loc :: CtLoc
  , u_defer :: TcRef Cts
  , u_unified :: Maybe (TcRef [Var])
  }

uKind_defer :: UnifyEnv -> TcKind -> TcKind -> TcM ()
uKind_defer (UE { u_loc = loc, u_defer = ref }) ki1 ki2 = do
  let ct = mkNonCanonical
           $ CtWantedKind { ctev_pred = WantKindEq ki1 ki2
                          , ctev_loc = loc }
  updTcRef ref (`snocBag` ct)
  whenDOptM Opt_D_dump_tc_trace $ do
    ctxt <- getErrCtxt
    doc <- mkErrInfo emptyTidyEnv ctxt
    traceTc "uKind_defer" (vcat [ debugPprKind ki1, debugPprKind ki2, doc ])

uKind :: UnifyEnv -> TcKind -> TcKind -> TcM ()
uKind env orig_ki1 orig_ki2 = do
  tclvl <- getTcLevel
  traceTc "u_tys"
    $ vcat [ text "tclvl" <+> ppr tclvl
           , sep [ ppr orig_ki1, text "~", ppr orig_ki2 ] ]
  go orig_ki1 orig_ki2
  where   
    go :: TcKind -> TcKind -> TcM ()
    go (KiVarKi kv1) ki2 = do
      lookup_res <- isFilledMetaKiVar_maybe kv1
      case lookup_res of
        Just ki1 -> do traceTc "found filled kivar" (ppr kv1 <+> text ":->" <+> ppr ki1)
                       uKind env ki1 orig_ki2
        Nothing -> uUnfilledKiVar env NotSwapped kv1 ki2

    go ki1 (KiVarKi kv2) = do
      lookup_res <- isFilledMetaKiVar_maybe kv2
      case lookup_res of
        Just ki2 -> do traceTc "found filled kivar" (ppr kv2 <+> text ":->" <+> ppr ki2)
                       uKind env orig_ki1 ki2
        Nothing -> uUnfilledKiVar env IsSwapped kv2 ki1

    go UKd UKd = return ()
    go AKd AKd = return ()
    go LKd LKd = return ()

    go (FunKd FKF_K_K arg1 res1) (FunKd FKF_K_K arg2 res2) = do
      uKind env arg1 arg2
      uKind env res1 res2

    go ki1 ki2 = defer ki1 ki2

    ------------------
    defer ki1 ki2
      | ki1 `tcEqKind` ki2 = return ()
      | otherwise = uKind_defer env orig_ki1 orig_ki2

{- *********************************************************************
*                                                                      *
                 uUnfilledVar and friends
*                                                                      *
********************************************************************* -}

uUnfilledKiVar :: UnifyEnv -> SwapFlag -> TcKiVar -> TcKind -> TcM ()
uUnfilledKiVar env swapped kv1 ki2 = do
  ki2 <- liftZonkM $ zonkTcKind ki2
  uUnfilledKiVar1 env swapped kv1 ki2

uUnfilledKiVar1 :: UnifyEnv -> SwapFlag -> TcKiVar -> TcKind -> TcM ()
uUnfilledKiVar1 env swapped kv1 ki2
  | Just kv2 <- getKiVar_maybe ki2
  = go kv2
  | otherwise
  = uUnfilledKiVar2 env swapped kv1 ki2
  where
    go kv2
      | kv1 == kv2
      = return ()
      | swapOverKiVars False kv1 kv2
      = uUnfilledKiVar2 env (flipSwap swapped) kv2 (mkKiVarKi kv1)
      | otherwise
      = uUnfilledKiVar2 env swapped kv1 ki2

uUnfilledKiVar2 :: UnifyEnv -> SwapFlag -> TcKiVar -> TcKind -> TcM ()
uUnfilledKiVar2 env swapped kv1 ki2 = do
  cur_lvl <- getTcLevel
  if not (touchabilityAndShapeTestKind cur_lvl kv1 ki2
          && simpleUnifyCheckKind kv1 ki2)
    then not_ok_so_defer
    else do liftZonkM $ writeMetaKiVar kv1 ki2
            case u_unified env of
              Nothing -> return ()
              Just uref -> updTcRef uref (kv1 :)
  where
    ki1 = mkKiVarKi kv1
    defer = unSwap swapped (uKind_defer env) ki1 ki2
    not_ok_so_defer = do
      traceTc "uUnfilledVar2 not ok" (ppr kv1 $$ ppr ki2)
      defer            

swapOverKiVars :: Bool -> TcKiVar -> TcKiVar -> Bool
swapOverKiVars is_given kv1 kv2
  | not is_given, pri1 == 0, pri2 > 0 = True
  | not is_given, pri2 == 0, pri1 > 0 = False

  | lvl1 `strictlyDeeperThan` lvl2 = False
  | lvl2 `strictlyDeeperThan` lvl1 = True

  | pri1 > pri2 = False
  | pri2 > pri1 = True

  | isSystemName kv2_name, not (isSystemName kv1_name) = True

  | otherwise = False
  where
    lvl1 = tcKiVarLevel kv1
    lvl2 = tcKiVarLevel kv2
    pri1 = lhsKiPriority kv1
    pri2 = lhsKiPriority kv2
    kv1_name = Var.varName kv1
    kv2_name = Var.varName kv2

lhsKiPriority :: TcKiVar -> Int
lhsKiPriority kv = assertPpr (isKiVar kv) (ppr kv) $
  case tcKiVarDetails kv of
    SkolemKv {} -> 0
    MetaKv { mkv_info = info } -> case info of
                                    KiVarKv -> 1
                                    TauKv -> 3

{- *********************************************************************
*                                                                      *
                 Checking alpha ~ ki
              for the on-the-fly unifier
*                                                                      *
********************************************************************* -}

simpleUnifyCheckKind  :: TcKiVar -> TcKind -> Bool
simpleUnifyCheckKind lhs_kv rhs = go rhs
  where
    lhs_kv_lvl = tcKiVarLevel lhs_kv

    go (KiVarKi kv)
      | lhs_kv == kv = False
      | tcKiVarLevel kv > lhs_kv_lvl = False
      | otherwise = True

    go (FunKd { fk_af = af, kft_arg = a, kft_res = r })
      | af == FKF_C_K = False
      | otherwise = go a && go r

    go (KdContext {}) = panic "simpleUnifyCheckKind"

    go UKd = True
    go AKd = True
    go LKd = True


touchabilityAndShapeTestKind :: TcLevel -> TcKiVar -> TcKind -> Bool
touchabilityAndShapeTestKind given_eq_lvl kv rhs
  | MetaKv { mkv_info = info, mkv_tclvl = kv_lvl } <- tcKiVarDetails kv
  , checkTopShapeKind info rhs
  = kv_lvl `deeperThanOrSame` given_eq_lvl
  | otherwise
  = False

checkTopShapeKind :: MetaInfoK -> TcKind -> Bool
checkTopShapeKind info xi
  = case info of
      KiVarKv -> case getKiVar_maybe xi of
                   Nothing -> False
                   Just kv -> case tcKiVarDetails kv of
                                SkolemKv {} -> True
                                MetaKv { mkv_info = KiVarKv } -> True
                                _ -> False
      _ -> True
