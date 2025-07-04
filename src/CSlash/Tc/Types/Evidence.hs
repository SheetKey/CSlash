{-# LANGUAGE FlexibleContexts #-}

module CSlash.Tc.Types.Evidence where

import Prelude hiding ((<>))

import CSlash.Types.Unique.DFM
import CSlash.Types.Unique.FM
import CSlash.Types.Var
-- import GHC.Types.Id( idScaledType )
-- import GHC.Core.Coercion.Axiom
-- import GHC.Core.Coercion
import CSlash.Core.Ppr ()   -- Instance OutputableBndr TyVar
import CSlash.Tc.Utils.TcType
import CSlash.Core.Type
import CSlash.Core.Type.FVs
import CSlash.Core.Kind
import CSlash.Core.TyCon
import CSlash.Core.DataCon ( DataCon{-, dataConWrapId-} )
import CSlash.Builtin.Names
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Core.Predicate
import CSlash.Types.Basic

import CSlash.Core
-- import GHC.Core.Class (Class, classSCSelId )
-- import GHC.Core.FVs   ( exprSomeFreeVars )
-- import GHC.Core.InstEnv ( Canonical )

import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Outputable

import CSlash.Data.Bag
import CSlash.Data.FastString

import qualified Data.Data as Data
import CSlash.Types.SrcLoc
import Data.IORef( IORef )
import CSlash.Types.Unique.Set
-- import GHC.Core.Multiplicity

import qualified Data.Semigroup as S

maybeSymCo :: SwapFlag -> KindCoercion kv -> KindCoercion kv
maybeSymCo IsSwapped co = mkSymKiCo co
maybeSymCo NotSwapped co = co

{- *********************************************************************
*                                                                      *
                  CsWrapper
*                                                                      *
********************************************************************* -}
  
data CsWrapper
  = WpHole
  | WpCompose CsWrapper CsWrapper
  | WpTyLam (AnyTyVar AnyKiVar) -- can probably be 'TcTyVar AnyKiVar' (these should be skols)
  | WpKiLam AnyKiVar            -- "             " 'TcKiVar'          "                     "

(<.>) :: CsWrapper -> CsWrapper -> CsWrapper
WpHole <.> c = c
c <.> WpHole = c
c1 <.> c2 = c1 `WpCompose` c2

idCsWrapper :: CsWrapper
idCsWrapper = WpHole

mkWpTyLams :: [AnyTyVar AnyKiVar] -> CsWrapper
mkWpTyLams tvs = mk_lam_fn WpTyLam tvs

mkWpKiLams :: [AnyKiVar] -> CsWrapper
mkWpKiLams kvs = mk_lam_fn WpKiLam kvs

mk_lam_fn :: (a -> CsWrapper) -> [a] -> CsWrapper
mk_lam_fn f as = foldr (\x wrap -> f x <.> wrap) WpHole as

{- *********************************************************************
*                                                                      *
                  Evidence bindings
*                                                                      *
********************************************************************* -}
  
data TcKiEvBinds
  = TcKiEvBinds KiEvBindsVar
  | KiEvBinds (Bag KiEvBind)

data KiEvBindsVar
  = KiEvBindsVar
    { kebv_uniq :: Unique
    , kebv_binds :: IORef KiEvBindMap
    , kebv_kcvs :: IORef (MkVarSet (KiCoVar AnyKiVar))
    }

newtype KiEvBindMap = KiEvBindMap { kev_bind_varenv :: MkDVarEnv (KiCoVar AnyKiVar) KiEvBind }

emptyKiEvBindMap :: KiEvBindMap
emptyKiEvBindMap = KiEvBindMap emptyDVarEnv

extendKiEvBinds :: KiEvBindMap -> KiEvBind -> KiEvBindMap
extendKiEvBinds bs kev_bind
  = KiEvBindMap { kev_bind_varenv = extendDVarEnv
                                     (kev_bind_varenv bs)
                                     (keb_lhs kev_bind)
                                     kev_bind }

isEmptyKiEvBindMap :: KiEvBindMap -> Bool
isEmptyKiEvBindMap (KiEvBindMap m) = isEmptyDVarEnv m

lookupKiEvBind :: KiEvBindMap -> KiEvVar AnyKiVar -> Maybe KiEvBind
lookupKiEvBind bs = lookupDVarEnv (kev_bind_varenv bs)

kiEvBindMapBinds :: KiEvBindMap -> Bag KiEvBind
kiEvBindMapBinds = foldKiEvBindMap consBag emptyBag

foldKiEvBindMap :: (KiEvBind -> a -> a) -> a -> KiEvBindMap -> a
foldKiEvBindMap k z bs = foldDVarEnv k z (kev_bind_varenv bs)

nonDetStrictFoldKiEvBindMap :: (KiEvBind -> a -> a) -> a -> KiEvBindMap -> a
nonDetStrictFoldKiEvBindMap k z bs = nonDetStrictFoldDVarEnv k z (kev_bind_varenv bs)

filterKiEvBindMap :: (KiEvBind -> Bool) -> KiEvBindMap -> KiEvBindMap
filterKiEvBindMap k (KiEvBindMap { kev_bind_varenv = env })
  = KiEvBindMap { kev_bind_varenv = filterDVarEnv k env }

varSetMinusKiEvBindMap
  :: MkVarSet (KiCoVar AnyKiVar) -> KiEvBindMap -> MkVarSet (KiCoVar AnyKiVar)
varSetMinusKiEvBindMap vs (KiEvBindMap dve) = vs `uniqSetMinusUDFM` dve

instance Outputable KiEvBindMap where
  ppr (KiEvBindMap m) = ppr m

data KiEvBind = KiEvBind
  { keb_lhs :: KiEvVar AnyKiVar
  , keb_rhs :: KiEvType
  , keb_info :: KiEvBindInfo
  }

kiEvBindVar :: KiEvBind -> KiEvVar AnyKiVar
kiEvBindVar = keb_lhs

mkWantedKiEvBind :: KiEvVar AnyKiVar -> Bool -> KiEvType -> KiEvBind
mkWantedKiEvBind ev c tm = KiEvBind { keb_info = KiEvBindWanted c, keb_lhs = ev, keb_rhs = tm }

mkGivenKiEvBind :: KiEvVar AnyKiVar -> KiEvType -> KiEvBind
mkGivenKiEvBind ev tm = KiEvBind { keb_info = KiEvBindGiven, keb_lhs = ev, keb_rhs = tm }

data KiEvBindInfo
  = KiEvBindGiven
  | KiEvBindWanted { kebi_canonical :: Bool }

-- 'EvTerm' in GHC
type KiEvType = Type (KiEvVar AnyKiVar) AnyKiVar

kiEvVar :: KiEvVar AnyKiVar -> KiEvType
kiEvVar = TyVarTy

kiEvCoercion :: KindCoercion AnyKiVar -> KiEvType
kiEvCoercion co = KindCoercion co

kiEvCast :: KiEvType -> KindCoercion AnyKiVar -> KiEvType
kiEvCast et co
  | isReflKiCo co = et
  | otherwise = CastTy et co

{- *********************************************************************
*                                                                      *
         Evidence for holes
*                                                                      *
********************************************************************* -}

mkKiEvCast :: KiEvType -> KindCoercion AnyKiVar -> KiEvType
mkKiEvCast ev lco
  | isReflKiCo lco = ev
  | otherwise = kiEvCast ev lco

emptyTcKiEvBinds :: TcKiEvBinds
emptyTcKiEvBinds = KiEvBinds emptyBag

kiEvTypeCoercion_maybe :: KiEvType -> Maybe (KindCoercion AnyKiVar)
kiEvTypeCoercion_maybe ev_ty = go ev_ty
  where
    go (TyVarTy v) = return $ mkKiCoVarCo v
    go (KindCoercion co) = return co
    go ct@(CastTy {}) = pprPanic "kiEvTypeCoercion_maybe" (ppr ct)
    go _ = Nothing

{- *********************************************************************
*                                                                      *
                  Free variables
*                                                                      *
********************************************************************* -}

findNeededKiEvVars :: KiEvBindMap -> MkVarSet (KiEvVar AnyKiVar) -> MkVarSet (KiEvVar AnyKiVar)
findNeededKiEvVars ev_binds seeds = transCloVarSet also_needs seeds
  where
    also_needs needs = nonDetStrictFoldUniqSet add emptyVarSet needs

    add v needs
      | Just ev_bind <- lookupKiEvBind ev_binds v
      , KiEvBind { keb_info = KiEvBindGiven, keb_rhs = rhs } <- ev_bind
      = kiEvVarsOfType rhs `unionVarSet` needs
      | otherwise
      = needs

kiEvVarsOfType :: KiEvType -> MkVarSet (KiEvVar AnyKiVar)
kiEvVarsOfType = fst . typeSomeFreeVars fv_cand
  where
    fv_cand (Left tv) = isKiEvVarKind $ varKind tv
    fv_cand (Right _) = False

{- *********************************************************************
*                                                                      *
                  Pretty printing
*                                                                      *
********************************************************************* -}

instance Outputable TcKiEvBinds where
  ppr (TcKiEvBinds v) = ppr v
  ppr (KiEvBinds bs) = text "KiEvBinds" <> braces (vcat (map ppr (bagToList bs)))

instance Outputable KiEvBindsVar where
  ppr (KiEvBindsVar { kebv_uniq = u }) = text "KiEvBindsVar" <> angleBrackets (ppr u)

instance Outputable KiEvBind where
  ppr (KiEvBind { keb_lhs = v, keb_rhs = e, keb_info = info })
    = sep [ pp_gw <+> ppr v, nest 2 $ equals <+> ppr e ]
    where
      pp_gw = brackets $ case info of
                           KiEvBindGiven -> char 'G'
                           KiEvBindWanted {} -> char 'W'
