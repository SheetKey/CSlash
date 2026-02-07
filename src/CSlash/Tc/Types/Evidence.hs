{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}

module CSlash.Tc.Types.Evidence where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

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

maybeSymTyCo :: SwapFlag -> TypeCoercion p -> TypeCoercion p
maybeSymTyCo IsSwapped co = mkSymTyCo co
maybeSymTyCo NotSwapped co = co

maybeSymKiCo :: SwapFlag -> KindCoercion p -> KindCoercion p
maybeSymKiCo IsSwapped co = mkSymKiCo co
maybeSymKiCo NotSwapped co = co

{- *********************************************************************
*                                                                      *
                  CsWrapper
*                                                                      *
********************************************************************* -}

data CsWrapper p
  = WpHole
  | WpCompose (CsWrapper p) (CsWrapper p)
  | WpFun (CsWrapper p) (MonoKind p) (Type p)
    -- given 'A -> B', the wrapper is on 'B' and the type is 'A', and the kind is the fun kind
  | WpCast (TypeCoercion p)
  | WpTyLam (TyVar p)
  | WpKiCoLam (KiCoVar p)
  | WpKiLam (KiVar p)
  | WpTyApp (Type p)
  | WpKiApp (MonoKind p)
  | WpKiCoApp (KindCoercion p)
  | WpMultCoercion (KindCoercion p)
  deriving Data.Data
{- TODO: 'Wp..Lam' could have TcTyVar, TcKiCoVar, TcKiVar when p~Tc
since these wrappers are created with freshly instantiated skolem vars (proper TcVars)
However, this would require change to the current phase system (probably a new phase).
Or, the CsWrapper would need a different phase. This would complicate zonking.
Or, the CsWrapper could become a GADT (Probably would cause too much duplication).
-}

(<.>) :: CsWrapper p -> CsWrapper p -> CsWrapper p
WpHole <.> c = c
c <.> WpHole = c
c1 <.> c2 = c1 `WpCompose` c2

mkWpFun :: HasPass p pass => CsWrapper p -> MonoKind p -> Type p -> CsWrapper p
mkWpFun WpHole _ _ = WpHole
mkWpFun (WpCast res_co) fun_ki arg_ty = WpCast (mk_wp_fun_co fun_ki (mkReflTyCo arg_ty) res_co)
mkWpFun co fun_ki arg_ty = WpFun co fun_ki arg_ty

mk_wp_fun_co :: HasPass p pass => MonoKind p -> TypeCoercion p -> TypeCoercion p -> TypeCoercion p
mk_wp_fun_co fun_ki arg_co res_co = mkTyFunCo (mkReflKiCo fun_ki) arg_co res_co

mkWpCast :: TypeCoercion p -> CsWrapper p
mkWpCast co
  | isReflTyCo co = WpHole
  | otherwise = WpCast co

idCsWrapper :: CsWrapper p
idCsWrapper = WpHole

isIdCsWrapper :: CsWrapper p -> Bool
isIdCsWrapper WpHole = True
isIdCsWrapper _ = False

mkWpTyApps :: [Type p] -> CsWrapper p
mkWpTyApps tys = mk_co_app_fn WpTyApp tys

mkWpKiApps :: [MonoKind p] -> CsWrapper p
mkWpKiApps kis = mk_co_app_fn WpKiApp kis

mkWpKiCoApps :: [KindCoercion p] -> CsWrapper p
mkWpKiCoApps args = mk_co_app_fn WpKiCoApp args

mkWpTyLams :: [TyVar p] -> CsWrapper p
mkWpTyLams tvs = mk_lam_fn WpTyLam tvs

mkWpKiCoLams :: [KiCoVar p] -> CsWrapper p
mkWpKiCoLams tvs = mk_lam_fn WpKiCoLam tvs

mkWpKiLams :: [KiVar p] -> CsWrapper p
mkWpKiLams kvs = mk_lam_fn WpKiLam kvs

mk_lam_fn :: (a -> CsWrapper p) -> [a] -> CsWrapper p
mk_lam_fn f as = foldr (\x wrap -> f x <.> wrap) WpHole as

mk_co_app_fn :: (a -> CsWrapper p) -> [a] -> CsWrapper p
mk_co_app_fn f as = foldr (\x wrap -> wrap <.> f x) WpHole as

{- *********************************************************************
*                                                                      *
                  Evidence bindings
*                                                                      *
********************************************************************* -}

data KiCoBindsVar
  = KiCoBindsVar
    { kcbv_uniq :: Unique
    , kcbv_kcvs :: IORef (KiCoVarSet Tc)
    }

data TyCoBindsVar
  = TyCoBindsVar
    { tcbv_uniq :: Unique
    , tcbv_tcvs :: IORef (TyCoVarSet Tc)
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

instance IsPass p => Outputable (CsWrapper (CsPass p)) where
  ppr co_fn = pprCsWrapper co_fn (no_parens (text "<>"))

pprCsWrapper :: HasPass p pass => CsWrapper p -> (Bool -> SDoc) -> SDoc
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
