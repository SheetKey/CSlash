{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveDataTypeable #-}
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
import CSlash.Core.Type.Rep (TypeCoercion, mkReflTyCo, isReflTyCo, mkSymTyCo)
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

maybeSymTyCo :: SwapFlag -> TypeCoercion tv kv -> TypeCoercion tv kv
maybeSymTyCo IsSwapped co = mkSymTyCo co
maybeSymTyCo NotSwapped co = co

maybeSymKiCo :: SwapFlag -> KindCoercion kv -> KindCoercion kv
maybeSymKiCo IsSwapped co = mkSymKiCo co
maybeSymKiCo NotSwapped co = co

{- *********************************************************************
*                                                                      *
                  CsWrapper
*                                                                      *
********************************************************************* -}

type AnyCsWrapper = CsWrapper (AnyTyVar AnyKiVar) AnyKiVar
type ZkCsWrapper = CsWrapper (TyVar KiVar) KiVar

data CsWrapper tv kv
  = WpHole
  | WpCompose (CsWrapper tv kv) (CsWrapper tv kv)
  | WpFun (CsWrapper tv kv) (MonoKind kv) (Type tv kv)
    -- given 'A -> B', the wrapper is on 'B' and the type is 'A', and the kind is the fun kind
  | WpCast (TypeCoercion tv kv)
  | WpTyLam tv            -- can probably be 'TcTyVar AnyKiVar' (these should be skols)
  | WpKiLam kv            -- "             " 'TcKiVar'          "                     "
  | WpTyApp (Type tv kv)
  | WpKiApp (MonoKind kv)
  | WpKiCoApp (KindCoercion kv)
  | WpMultCoercion (KindCoercion kv)
  deriving Data.Data

(<.>) :: CsWrapper tv kv -> CsWrapper tv kv -> CsWrapper tv kv
WpHole <.> c = c
c <.> WpHole = c
c1 <.> c2 = c1 `WpCompose` c2

mkWpFun :: IsTyVar tv kv => CsWrapper tv kv -> MonoKind kv -> Type tv kv -> CsWrapper tv kv
mkWpFun WpHole _ _ = WpHole
mkWpFun (WpCast res_co) fun_ki arg_ty = WpCast (mk_wp_fun_co fun_ki (mkReflTyCo arg_ty) res_co)
mkWpFun co fun_ki arg_ty = WpFun co fun_ki arg_ty

mk_wp_fun_co
  :: IsTyVar tv kv
  => MonoKind kv -> TypeCoercion tv kv -> TypeCoercion tv kv -> TypeCoercion tv kv
mk_wp_fun_co fun_ki arg_co res_co = mkTyFunCo (mkReflKiCo fun_ki) arg_co res_co

mkWpCast :: TypeCoercion tv kv -> CsWrapper tv kv
mkWpCast co
  | isReflTyCo co = WpHole
  | otherwise = WpCast co

idCsWrapper :: CsWrapper tv kv
idCsWrapper = WpHole

isIdCsWrapper :: CsWrapper tv kv -> Bool
isIdCsWrapper WpHole = True
isIdCsWrapper _ = False

mkWpTyApps :: [Type tv kv] -> CsWrapper tv kv
mkWpTyApps tys = mk_co_app_fn WpTyApp tys

mkWpKiApps :: [MonoKind kv] -> CsWrapper tv kv
mkWpKiApps kis = mk_co_app_fn WpKiApp kis

mkWpKiCoApps :: [KindCoercion kv] -> CsWrapper tv kv
mkWpKiCoApps args = mk_co_app_fn WpKiCoApp args

mkWpTyLams :: [tv] -> CsWrapper tv kv
mkWpTyLams tvs = mk_lam_fn WpTyLam tvs

mkWpKiLams :: [kv] -> CsWrapper tv kv
mkWpKiLams kvs = mk_lam_fn WpKiLam kvs

mk_lam_fn :: (a -> CsWrapper tv kv) -> [a] -> CsWrapper tv kv
mk_lam_fn f as = foldr (\x wrap -> f x <.> wrap) WpHole as

mk_co_app_fn :: (a -> CsWrapper tv kv) -> [a] -> CsWrapper tv kv
mk_co_app_fn f as = foldr (\x wrap -> wrap <.> f x) WpHole as

{- *********************************************************************
*                                                                      *
                  Evidence bindings
*                                                                      *
********************************************************************* -}

data KiCoBindsVar
  = KiCoBindsVar
    { kcbv_uniq :: Unique
    , kcbv_kcvs :: IORef (MkVarSet (KiCoVar AnyKiVar))
    }

data TyCoBindsVar
  = TyCoBindsVar
    { tcbv_uniq :: Unique
    , tcbv_tcvs :: IORef (MkVarSet (TyCoVar (AnyTyVar AnyKiVar) AnyKiVar))
    }

{- *********************************************************************
*                                                                      *
         Evidence for holes
*                                                                      *
********************************************************************* -}

{- *********************************************************************
*                                                                      *
                  Free variables
*                                                                      *
********************************************************************* -}

{- *********************************************************************
*                                                                      *
                  Pretty printing
*                                                                      *
********************************************************************* -}

instance IsTyVar tv kv => Outputable (CsWrapper tv kv) where
  ppr co_fn = pprCsWrapper co_fn (no_parens (text "<>"))

pprCsWrapper :: IsTyVar tv kv => CsWrapper tv kv -> (Bool -> SDoc) -> SDoc
pprCsWrapper wrap pp_thing_inside =
  sdocOption sdocPrintTypecheckerElaboration $ \case
  True -> help pp_thing_inside wrap False
  False -> pp_thing_inside False
  where
    -- help :: (Bool -> SDoc) -> CsWrapper -> Bool -> SDoc
    help it WpHole = it
    help it (WpCompose f1 f2) = help (help it f2) f1
    help it (WpFun f2 fki ty1) =
      add_parens ((parens (text "\\(x" <> colon <> ppr ty1 <> text ")."
                           <+> help (\_ -> it True <+> text "x") f2 False))
                   <+> colon <+> ppr fki)
    help it _ = panic "pprCsWrapper"

add_parens :: SDoc -> Bool -> SDoc
add_parens d True = parens d
add_parens d False = d

no_parens :: SDoc -> Bool -> SDoc
no_parens d _ = d

instance Outputable KiCoBindsVar where
  ppr (KiCoBindsVar { kcbv_uniq = u }) = text "KiCoBindsVar" <> angleBrackets (ppr u)
