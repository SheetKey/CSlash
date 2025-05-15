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
import CSlash.Core.Kind
import CSlash.Core.TyCon
import CSlash.Core.DataCon ( DataCon{-, dataConWrapId-} )
import CSlash.Builtin.Names
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
-- import GHC.Core.Predicate
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

maybeSymCo :: SwapFlag -> KindCoercion -> KindCoercion
maybeSymCo IsSwapped co = mkSymKiCo co
maybeSymCo NotSwapped co = co

{- *********************************************************************
*                                                                      *
                  Evidence bindings
*                                                                      *
********************************************************************* -}
  
data KiEvBindsVar
  = KiEvBindsVar
    { kebv_uniq :: Unique
    , kebv_binds :: IORef KiEvBindMap
    , kebv_kcvs :: IORef KiCoVarSet
    }
  | KiCoEvBindsVar
    { kebv_uniq :: Unique
    , kebv_kcvs :: IORef KiCoVarSet
    }

isKiCoEvBindsVar :: KiEvBindsVar -> Bool 
isKiCoEvBindsVar (KiCoEvBindsVar {}) = True
isKiCoEvBindsVar (KiEvBindsVar {}) = False

newtype KiEvBindMap = KiEvBindMap { kev_bind_varenv :: DVarEnv KiEvBind }

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

lookupKiEvBind :: KiEvBindMap -> KiEvVar -> Maybe KiEvBind
lookupKiEvBind bs = lookupDVarEnv (kev_bind_varenv bs)

kiEvBindMapBinds :: KiEvBindMap -> Bag KiEvBind
kiEvBindMapBinds = foldKiEvBindMap consBag emptyBag

foldKiEvBindMap :: (KiEvBind -> a -> a) -> a -> KiEvBindMap -> a
foldKiEvBindMap k z bs = foldDVarEnv k z (kev_bind_varenv bs)

filterKiEvBindMap :: (KiEvBind -> Bool) -> KiEvBindMap -> KiEvBindMap
filterKiEvBindMap k (KiEvBindMap { kev_bind_varenv = env })
  = KiEvBindMap { kev_bind_varenv = filterDVarEnv k env }

instance Outputable KiEvBindMap where
  ppr (KiEvBindMap m) = ppr m

data KiEvBind = KiEvBind
  { keb_lhs :: KiEvVar
  , keb_rhs :: KiEvType
  , keb_info :: KiEvBindInfo
  }

kiEvBindVar :: KiEvBind -> KiEvVar
kiEvBindVar = keb_lhs

mkWantedKiEvBind :: KiEvVar -> Bool -> KiEvType -> KiEvBind
mkWantedKiEvBind ev c tm = KiEvBind { keb_info = KiEvBindWanted c, keb_lhs = ev, keb_rhs = tm }

mkGivenKiEvBind :: KiEvVar -> KiEvType -> KiEvBind
mkGivenKiEvBind ev tm = KiEvBind { keb_info = KiEvBindGiven, keb_lhs = ev, keb_rhs = tm }

data KiEvBindInfo
  = KiEvBindGiven
  | KiEvBindWanted { kebi_canonical :: Bool }

-- 'EvTerm' in GHC
type KiEvType = Type

kiEvVar :: KiEvVar -> KiEvType
kiEvVar = TyVarTy

kiEvCoercion :: KindCoercion -> KiEvType 
kiEvCoercion co = KindCoercion co

kiEvCast :: KiEvType -> KindCoercion -> KiEvType
kiEvCast et co
  | isReflKiCo co = et
  | otherwise = CastTy et co

{- *********************************************************************
*                                                                      *
         Evidence for holes
*                                                                      *
********************************************************************* -}

mkKiEvCast :: KiEvType -> KindCoercion -> KiEvType
mkKiEvCast ev lco
  | isReflKiCo lco = ev
  | otherwise = kiEvCast ev lco

kiEvTypeCoercion_maybe :: KiEvType -> Maybe KindCoercion
kiEvTypeCoercion_maybe ev_ty = go ev_ty
  where
    go (TyVarTy v) = return $ mkKiCoVarCo v
    go (KindCoercion co) = return co
    go ct@(CastTy {}) = pprPanic "kiEvTypeCoercion_maybe" (ppr ct)
    go _ = Nothing

{- *********************************************************************
*                                                                      *
                  Pretty printing
*                                                                      *
********************************************************************* -}

instance Outputable KiEvBind where
  ppr (KiEvBind { keb_lhs = v, keb_rhs = e, keb_info = info })
    = sep [ pp_gw <+> ppr v, nest 2 $ equals <+> ppr e ]
    where
      pp_gw = brackets $ case info of
                           KiEvBindGiven -> char 'G'
                           KiEvBindWanted {} -> char 'W'
