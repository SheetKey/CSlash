{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}

module CSlash.Core.TyCon where

import Prelude hiding ((<>))

import {-# SOURCE #-} CSlash.Core.Type.Rep (Type, mkNakedTyConTy)
import {-# SOURCE #-} CSlash.Core.DataCon (DataCon, dataConFullSig, dataConArity)
import {-# SOURCE #-} CSlash.Core.Kind.Compare (tcEqKind)

import CSlash.Cs.Pass

import CSlash.Core.Kind

import CSlash.Utils.Binary
import CSlash.Types.Var.TyVar
import CSlash.Types.Var.KiVar
import CSlash.Types.Basic
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Builtin.Names
import CSlash.Data.Maybe
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Data.FastString.Env
import CSlash.Utils.Misc
import CSlash.Types.Unique.Set
import CSlash.Unit.Module

import qualified Data.Data as Data

{- *********************************************************************
*                                                                      *
                    TyConBinder
*                                                                      *
********************************************************************* -}

{- TODO:
This binder may be for arguments to the *TC*:
since kinds are types in GHC,
it may be that kind arguments are considered 'Infered' (not 'Specified' or 'Required')
while type arguemnts (whose kinds are provided by kind arguments)
are considered 'Required'.
WE DON'T DO THIS:
All arguments to a type constructor are required.
This might need to change here, i.e., 'type TyConBinder = TypeVar'.
This change should be reflected in Iface.Type

-}
-- type TyConBinder = VarBndr TypeVar ForAllTyFlag

-- verifyTyConKind :: [TyConBinder] -> Kind -> Kind
-- verifyTyConKind bndrs kind =
--   let kind' = remove_constrs kind
--   in if no_constrs kind'
--      then if go bndrs kind'
--           then kind
--           else panic "verifyTyConKind"
--      else panic "verifyTyConKind"
--   where
--     remove_constrs (FunKd _ (KdContext _) k2) = remove_constrs k2
--     remove_constrs (KdContext _) = panic "remove_constrs"
--     remove_constrs k = k

--     no_constrs (KdContext _) = False
--     no_constrs (FunKd FKF_C_K _ _) = False
--     no_constrs (FunKd _ k1 k2) = no_constrs k1 && no_constrs k2 -- this shouldn't be necessary
--                                                                 -- if there are constraints
--                                                                 -- they should only appear
--                                                                 -- once and at the 'top'
--     no_constrs _ = True

--     go [] (KiVarKi {}) = True
--     go [] (KiCon _) = True
--     go [Bndr tv _] (FunKd _ arg_kd _)
--       | isTyVar tv = varKind tv `tcEqKind` arg_kd
--     go ((Bndr tv _):bndrs) (FunKd _ arg_kd res_kd)
--       | isTyVar tv = varKind tv `tcEqKind` arg_kd && go bndrs res_kd
--     go _ _ = pprPanic "verifyTyConKind_go" (vcat [ppr bndrs, ppr kind])

-- mkAnonTyConBinder :: TypeVar -> TyConBinder
-- mkAnonTyConBinder tv = assert (isTyVar tv) $
--                        Bndr tv AnonTCB

-- mkAnonTyConBinders :: [TypeVar] -> [TyConBinder]
-- mkAnonTyConBinders = map mkAnonTyConBinder

-- mkNamedTyConBinder :: ForAllTyFlag -> TypeVar -> TyConBinder
-- mkNamedTyConBinder vis tv = assert (isTyVar tv) $
--                             Bndr tv (NamedTCB vis)

-- mkNamedTyConBinders :: ForAllTyFlag -> [TypeVar] -> [TyConBinder]
-- mkNamedTyConBinders vis tvs = map (mkNamedTyConBinder vis) tvs

-- use like ghc mkAnonTyConBinder
-- mkSpecifiedTyConBinder :: TypeVar -> TyConBinder
-- mkSpecifiedTyConBinder tv = assert (isTyVar tv) $
--                             Bndr tv Specified

-- mkSpecifiedTyConBinders :: [TypeVar] -> [TyConBinder]
-- mkSpecifiedTyConBinders tvs = map mkSpecifiedTyConBinder tvs

mkTyConTy :: TyCon p -> Type p
mkTyConTy tycon = tyConNullaryTy tycon

{- *********************************************************************
*                                                                      *
               The TyCon type
*                                                                      *
********************************************************************* -}

type MonoTyCon = TyCon
type PolyTyCon = TyCon

data TyCon p = TyCon
  { tyConUnique :: !Unique
  , tyConName :: !Name
  , tyConArity :: Arity
  , tyConNullaryTy :: Type p
  , tyConDetails :: !(TyConDetails p)
  }

data TyConDetails p where
  AlgTyCon ::
    { algTcRhs :: AlgTyConRhs
    , algTcFlavor :: AlgTyConFlav
    , tyConKind :: Kind Zk
    } -> TyConDetails p
  SynonymTyCon ::
    { synTcRhs :: Type Zk
    , synIsTau :: Bool
    , synIsForgetful :: Bool
    , synIsConcrete :: Bool
    , tyConKind :: Kind Zk
    } -> TyConDetails p
  PrimTyCon :: { tyConKind :: Kind Zk } -> TyConDetails p
  TcTyCon :: -- used during type checking only
    { tctc_scoped_kvs :: [(Name, TcKiVar)]
    , tctc_is_poly :: Bool
    , tctc_flavor :: TyConFlavor
    , tcTyConKind :: Kind Tc -- TODO this could be Either (MonoKind Tc) (Kind Tc), remove tctc_is_poly
    } -> TyConDetails Tc

toTcTyCon :: TyCon Zk -> TyCon Tc
toTcTyCon TyCon { tyConDetails = details, .. } = case details of
  AlgTyCon {..} -> let tc = TyCon { tyConNullaryTy = mkNakedTyConTy tc
                                  , tyConDetails = AlgTyCon {..}
                                  , .. }
                   in tc
  SynonymTyCon {..} -> let tc = TyCon { tyConNullaryTy = mkNakedTyConTy tc
                                      , tyConDetails = SynonymTyCon {..}
                                      , .. }
                       in tc
  PrimTyCon {..} -> let tc = TyCon { tyConNullaryTy = mkNakedTyConTy tc
                                   , tyConDetails = PrimTyCon {..}
                                   , .. }
                    in tc

-- instance AsAnyTy TyConDetails where
--   asAnyTy AlgTyCon { algTcRhs = rhs, .. } = AlgTyCon { algTcRhs = asAnyTy rhs, .. }
--   asAnyTy SynonymTyCon { synTcRhs = rhs, .. } = SynonymTyCon { synTcRhs = asAnyTy rhs, .. }
--   asAnyTy PrimTyCon = PrimTyCon
--   asAnyTy TcTyCon { .. } = TcTyCon { .. }

--   asAnyTyKi AlgTyCon { algTcRhs = rhs, .. } = AlgTyCon { algTcRhs = asAnyTyKi rhs, .. }
--   asAnyTyKi SynonymTyCon { synTcRhs = rhs, .. } = SynonymTyCon { synTcRhs = asAnyTyKi rhs, .. }
--   asAnyTyKi PrimTyCon = PrimTyCon
--   asAnyTyKi TcTyCon { .. } = TcTyCon { .. }

data AlgTyConRhs
  = AbstractTyCon
  | TupleTyCon { data_con :: DataCon Zk }
  | SumTyCon
    { data_cons :: [DataCon Zk]
    , data_cons_size :: Int
    }
  | DataTyCon
    { data_cons :: [DataCon Zk]
    , data_cons_size :: Int
    , is_enum :: Bool
    }

-- instance AsAnyTy AlgTyConRhs where
--   asAnyTy AbstractTyCon = AbstractTyCon
--   asAnyTy TupleTyCon { data_con = dc } = TupleTyCon $ asAnyTy dc
--   asAnyTy SumTyCon { data_cons = dcs, data_cons_size = size}
--     = SumTyCon (asAnyTy <$> dcs) size
--   asAnyTy DataTyCon { data_cons = dcs, .. }
--     = DataTyCon { data_cons = asAnyTy <$> dcs, .. }

mkSumTyConRhs :: [DataCon Zk] -> AlgTyConRhs
mkSumTyConRhs data_cons = SumTyCon data_cons (length data_cons)

mkDataTyConRhs :: [DataCon Zk] -> AlgTyConRhs
mkDataTyConRhs cons
  = DataTyCon
    { data_cons = cons
    , data_cons_size = length cons
    , is_enum = not (null cons) && all is_enum_con cons
    }
  where
    is_enum_con con = dataConArity con == 0
      
data AlgTyConFlav
  = VanillaAlgTyCon -- TyConRepName -- this name is for Typeable
  | AlgSumTyCon

instance Outputable AlgTyConFlav where
  ppr (VanillaAlgTyCon {}) = text "Vanilla ADT"
  ppr (AlgSumTyCon {}) = text "Sum"

isTcTyCon :: TyCon p -> Bool
isTcTyCon (TyCon { tyConDetails = details })
  | TcTyCon {} <- details = True
  | otherwise = False

setTcTyConKind :: TyCon Tc -> MonoKind Tc -> TyCon Tc
setTcTyConKind tc kind = assert (isMonoTcTyCon tc) $ case tyConDetails tc of
  details@TcTyCon{} -> 
    let tc' = tc { tyConDetails = details { tcTyConKind = Mono kind }
                 , tyConNullaryTy = mkNakedTyConTy tc' }
    in tc'
  _ -> pprPanic "setTcTyConKind" (ppr tc)
  
isMonoTcTyCon :: TyCon Tc -> Bool
isMonoTcTyCon (TyCon { tyConDetails = details })
  | TcTyCon { tctc_is_poly = is_poly } <- details = not is_poly
  | otherwise = False

monoTcTyConKind :: TyCon Tc -> Maybe (MonoKind Tc)
monoTcTyConKind tc@(TyCon { tyConDetails = details })
  | TcTyCon { tctc_is_poly = False, tcTyConKind = kind } <- details
  = case kind of
      Mono mki -> Just mki
      _ -> pprPanic "monoTcTyCon has non-mono kind" (ppr tc $$ ppr kind)
  | otherwise = Nothing

{- -------------------------------------------
--      Expand type-constructor applications
-------------------------------------------- -}

data ExpandSynResult p tyco
  = NoExpansion
  | ExpandsSyn [tyco] (Type Zk) [tyco]

expandSynTyCon_maybe :: TyCon p -> [tyco] -> ExpandSynResult p tyco
expandSynTyCon_maybe (TyCon { tyConArity = arity, tyConDetails = details }) cos
  | SynonymTyCon { synTcRhs = rhs } <- details
  = if arity == 0
    then ExpandsSyn [] rhs cos
    else case cos `listLengthCmp` arity of
           GT -> ExpandsSyn cos_1 rhs cos_2
           EQ -> ExpandsSyn cos_1 rhs cos_2
           LT -> NoExpansion
  | otherwise
  = NoExpansion
  where
    (cos_1, cos_2) = splitAt arity cos

{- *********************************************************************
*                                                                      *
            TyCon Construction
*                                                                      *
********************************************************************* -}

mkTyCon :: Name -> Arity -> TyConDetails p -> TyCon p
mkTyCon name arity details = tc
  where
    tc = TyCon { tyConUnique = nameUnique name
               , tyConName = name
               , tyConArity = arity
               , tyConNullaryTy = mkNakedTyConTy tc
               , tyConDetails = details
               }

mkAlgTyCon
  :: Name
  -> Kind Zk
  -> Arity
  -> AlgTyConRhs
  -> AlgTyConFlav
  -> TyCon p
mkAlgTyCon name kind arity rhs parent
  = mkTyCon name arity $
    AlgTyCon { algTcRhs = rhs
             , algTcFlavor = parent
             , tyConKind = kind }

mkTupleTyCon
  :: Name
  -> Kind Zk
  -> Arity
  -> DataCon Zk
  -> AlgTyConFlav
  -> TyCon p
mkTupleTyCon name kind arity con parent
  = mkTyCon name arity $
    AlgTyCon { algTcRhs = TupleTyCon { data_con = con }
             , algTcFlavor = parent
             , tyConKind = kind }

mkSumTyCon
  :: Name
  -> Kind Zk
  -> Arity
  -> [DataCon Zk]
  -> AlgTyConFlav
  -> TyCon p
mkSumTyCon name kind arity cons parent
  = mkTyCon name arity $
    AlgTyCon { algTcRhs = mkSumTyConRhs cons
             , algTcFlavor = parent
             , tyConKind = kind }

mkTcTyCon
  :: Name
  -> Kind Tc
  -> Arity
  -> [(Name, TcKiVar)]
  -> Bool
  -> TyConFlavor 
  -> TyCon Tc
mkTcTyCon name kind arity scoped_kvs poly flav
  = mkTyCon name arity 
    $ TcTyCon { tctc_scoped_kvs = scoped_kvs
              , tctc_is_poly = poly
              , tctc_flavor = flav
              , tcTyConKind = kind }

mkPrimTyCon :: Name -> Kind Zk -> Arity -> TyCon p
mkPrimTyCon name kind arity
  = mkTyCon name arity $ PrimTyCon kind

mkSynonymTyCon
  :: Name
  -> Kind Zk
  -> Arity
  -> Type Zk
  -> Bool -> Bool -> Bool
  -> TyCon p
mkSynonymTyCon name kind arity rhs is_tau is_forgetful is_concrete
  = mkTyCon name arity 
    $ SynonymTyCon { synTcRhs = rhs
                   , synIsTau = is_tau
                   , synIsForgetful = is_forgetful
                   , synIsConcrete = is_concrete
                   , tyConKind = kind }

isPrimTyCon :: TyCon p -> Bool
isPrimTyCon (TyCon { tyConDetails = details })
  | PrimTyCon {} <- details = True
  | otherwise = False

isAlgTyCon :: TyCon p -> Bool
isAlgTyCon (TyCon { tyConDetails = details })
  | AlgTyCon {} <- details = True
  | otherwise = False

isInjectiveTyCon :: TyCon p -> Bool
isInjectiveTyCon (TyCon { tyConDetails = details }) = go details
  where
    go (AlgTyCon{}) = True
    go (SynonymTyCon{}) = False
    go (PrimTyCon{}) = True
    go (TcTyCon{}) = True

isGenerativeTyCon :: TyCon p -> Bool
isGenerativeTyCon = isInjectiveTyCon

isTypeSynonymTyCon :: TyCon p -> Bool
isTypeSynonymTyCon (TyCon { tyConDetails = details })
  | SynonymTyCon{} <- details = True
  | otherwise = False
{-# INLINE isTypeSynonymTyCon #-}

isTauTyCon :: TyCon p -> Bool
isTauTyCon (TyCon { tyConDetails = details })
  | SynonymTyCon { synIsTau = is_tau } <- details = is_tau
  | otherwise = True

isForgetfulSynTyCon :: TyCon p -> Bool
isForgetfulSynTyCon (TyCon { tyConDetails = details })
  | SynonymTyCon { synIsForgetful = forget } <- details = forget
  | otherwise = False

tyConMustBeSaturated :: TyCon p -> Bool
tyConMustBeSaturated = tcFlavorMustBeSaturated . tyConFlavor

isTupleTyCon :: TyCon p -> Bool
isTupleTyCon (TyCon { tyConDetails = details })
  | AlgTyCon { algTcRhs = TupleTyCon {} } <- details = True
  | otherwise = False

isConcreteTyCon :: TyCon p -> Bool
isConcreteTyCon tc@(TyCon { tyConDetails = details })
  = case details of
      AlgTyCon {} -> True
      PrimTyCon {} -> True
      SynonymTyCon { synIsConcrete = is_conc } -> is_conc
      TcTyCon {} -> pprPanic "isConcreteTyCon" (ppr tc)

{- --------------------------------------------
--      TcTyCon
-------------------------------------------- -}

tcTyConScopedKiVars :: TyCon Tc -> [(Name, TcKiVar)]
tcTyConScopedKiVars tc@(TyCon { tyConDetails = details })
  | TcTyCon { tctc_scoped_kvs = scoped_kvs } <- details = scoped_kvs
  | otherwise = pprPanic "tcTyConScopedKiVars" (ppr tc)

tyConDataCons :: TyCon p -> [DataCon Zk]
tyConDataCons tycon = tyConDataCons_maybe tycon `orElse` []

tyConDataCons_maybe :: TyCon p -> Maybe [DataCon Zk]
tyConDataCons_maybe (TyCon { tyConDetails = details })
  | AlgTyCon { algTcRhs = rhs } <- details
  = case rhs of
      TupleTyCon { data_con = con } -> Just [con]
      SumTyCon { data_cons = cons } -> Just cons
      DataTyCon { data_cons = cons } -> Just cons
      AbstractTyCon -> Nothing
tyConDataCons_maybe _ = Nothing   

synTyConDefn_maybe :: TyCon p -> Maybe (Type Zk)
synTyConDefn_maybe (TyCon { tyConDetails = details })
  | SynonymTyCon {synTcRhs = ty} <- details
  = Just ty
  | otherwise
  = Nothing

synTyConRhs_maybe :: (TyCon p) -> Maybe (Type Zk)
synTyConRhs_maybe (TyCon { tyConDetails = details })
  | SynonymTyCon {synTcRhs = ty} <- details
  = Just ty
  | otherwise
  = Nothing

mkTyConTagMap :: (TyCon p) -> NameEnv ConTag
mkTyConTagMap tycon =
  mkNameEnv $ map getName (tyConDataCons tycon) `zip` [fIRST_TAG..]

{- *********************************************************************
*                                                                      *
            Instance declarations for TyCon
*                                                                      *
********************************************************************* -}

instance Eq (TyCon p) where
  a == b = getUnique a == getUnique b
  a /= b = getUnique a /= getUnique b

instance Uniquable (TyCon p) where
  getUnique tc = tyConUnique tc

instance Outputable (TyCon p) where
  ppr tc = ppr (tyConName tc) <> pp_tc
    where
      pp_tc = getPprStyle $ \ sty ->
              getPprDebug $ \ debug ->
                              if ((debug || dumpStyle sty) && isTcTyCon tc)
                              then text "[tc]"
                              else empty

pprTyConKind :: TyCon p -> SDoc
pprTyConKind tc = case tyConDetails tc of
  TcTyCon { tcTyConKind = kind } -> ppr kind
  other -> ppr $ tyConKind other

tyConFlavor :: TyCon p -> TyConFlavor
tyConFlavor (TyCon { tyConDetails = details })
  | AlgTyCon { algTcFlavor = parent, algTcRhs = rhs } <- details
  = case parent of
      _ -> case rhs of
             AbstractTyCon -> AbstractTypeFlavor
             TupleTyCon {} -> TupleFlavor
             SumTyCon {} -> SumFlavor
             DataTyCon {} -> DataTypeFlavor
  | SynonymTyCon {} <- details = TypeFunFlavor
  | PrimTyCon {} <- details = BuiltInTypeFlavor
  | TcTyCon { tctc_flavor = flav } <- details = flav

tcFlavorMustBeSaturated :: TyConFlavor -> Bool
tcFlavorMustBeSaturated TupleFlavor = False
tcFlavorMustBeSaturated SumFlavor = False
tcFlavorMustBeSaturated DataTypeFlavor = False
tcFlavorMustBeSaturated AbstractTypeFlavor = False
tcFlavorMustBeSaturated TypeFunFlavor = True
tcFlavorMustBeSaturated BuiltInTypeFlavor = False

instance NamedThing (TyCon p) where
  getName = tyConName

instance (Data.Typeable p) => Data.Data (TyCon p) where
  toConstr _ = abstractConstr "TyCon"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "TyCon"
