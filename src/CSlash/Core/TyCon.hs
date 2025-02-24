{-# LANGUAGE FlexibleInstances #-}

module CSlash.Core.TyCon where

import Prelude hiding ((<>))

import {-# SOURCE #-} CSlash.Core.Type.Rep (Type, mkNakedTyConTy)
import {-# SOURCE #-} CSlash.Core.DataCon (DataCon, dataConFullSig, dataConArity)

import CSlash.Core.Kind
import {-# SOURCE #-} CSlash.Core.Kind.Compare (tcEqKind)

import CSlash.Utils.Binary
import CSlash.Types.Var
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
type TyConBinder = VarBndr TypeVar ForAllTyFlag

verifyTyConKind :: [TyConBinder] -> Kind -> Kind
verifyTyConKind bndrs kind =
  let kind' = remove_constrs kind
  in if no_constrs kind'
     then if go bndrs kind'
          then kind
          else panic "verifyTyConKind"
     else panic "verifyTyConKind"
  where
    remove_constrs (FunKd _ (KdContext _) k2) = remove_constrs k2
    remove_constrs (KdContext _) = panic "remove_constrs"
    remove_constrs k = k

    no_constrs (KdContext _) = False
    no_constrs (FunKd FKF_C_K _ _) = False
    no_constrs (FunKd _ k1 k2) = no_constrs k1 && no_constrs k2 -- this shouldn't be necessary
                                                                -- if there are constraints
                                                                -- they should only appear
                                                                -- once and at the 'top'
    no_constrs _ = True

    go [] (KiVarKi {}) = True
    go [] UKd = True
    go [] AKd = True
    go [] LKd = True
    go [Bndr tv _] (FunKd _ arg_kd _)
      | isTyVar tv = varKind tv `tcEqKind` arg_kd
    go ((Bndr tv _):bndrs) (FunKd _ arg_kd res_kd)
      | isTyVar tv = varKind tv `tcEqKind` arg_kd && go bndrs res_kd
    go _ _ = pprPanic "verifyTyConKind_go" (vcat [ppr bndrs, ppr kind])

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
mkSpecifiedTyConBinder :: TypeVar -> TyConBinder
mkSpecifiedTyConBinder tv = assert (isTyVar tv) $
                            Bndr tv Specified

mkSpecifiedTyConBinders :: [TypeVar] -> [TyConBinder]
mkSpecifiedTyConBinders tvs = map mkSpecifiedTyConBinder tvs

mkTyConTy :: TyCon -> Type
mkTyConTy tycon = tyConNullaryTy tycon

{- *********************************************************************
*                                                                      *
               The TyCon type
*                                                                      *
********************************************************************* -}

data TyCon = TyCon
  { tyConUnique :: !Unique
  , tyConName :: !Name
  , tyConResKind :: Kind
  , tyConKind :: Kind
  , tyConArity :: Arity
  , tyConNullaryTy :: Type
  , tyConDetails :: !TyConDetails
  }

data TyConDetails
  = AlgTyCon
    -- { tyConCType :: Maybe CType
    -- , algTcGadtSyntax :: Bool
    { algTcRhs :: AlgTyConRhs
    -- , algTcFields :: FieldLabelEnv
    , algTcFlavor :: AlgTyConFlav
    }
  | SynonymTyCon
    { synTcRhs :: Type
    , synIsTau :: Bool
    , synIsForgetful :: Bool
    , synIsConcrete :: Bool
    }
  | PrimTyCon
    -- { primRepName :: TyConRepName } -- this is used to Typeable
  | TcTyCon -- used during type checking only
    { tctc_scoped_kvs :: [(Name, TcKiVar)]
    , tctc_is_poly :: Bool
    , tctc_flavor :: TyConFlavor TyCon
    }

data AlgTyConRhs
  = AbstractTyCon
  | TupleTyCon { data_con :: DataCon }
  | SumTyCon
    { data_cons :: [DataCon]
    , data_cons_size :: Int
    }
  | DataTyCon
    { data_cons :: [DataCon]
    , data_cons_size :: Int
    , is_enum :: Bool
    }

mkSumTyConRhs :: [DataCon] -> AlgTyConRhs
mkSumTyConRhs data_cons = SumTyCon data_cons (length data_cons)

mkDataTyConRhs :: [DataCon] -> AlgTyConRhs
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

isTcTyCon :: TyCon -> Bool
isTcTyCon (TyCon { tyConDetails = details })
  | TcTyCon {} <- details = True
  | otherwise = False

{- *********************************************************************
*                                                                      *
                 TyConRepName
*                                                                      *
********************************************************************* -}

type TyConRepName = Name

{- *********************************************************************
*                                                                      *
            TyCon Construction
*                                                                      *
********************************************************************* -}

mkTyCon :: Name -> Kind -> Kind -> Arity -> TyConDetails -> TyCon
mkTyCon name res_kind full_kind arity details = tc
  where
    tc = TyCon { tyConUnique = nameUnique name
               , tyConName = name
               , tyConResKind = res_kind
               , tyConKind = full_kind
               , tyConArity = arity
               , tyConNullaryTy = mkNakedTyConTy tc
               , tyConDetails = details
               }

mkAlgTyCon
  :: Name
  -> Kind
  -> Kind
  -> Arity
  -> AlgTyConRhs
  -> AlgTyConFlav
  -> TyCon
mkAlgTyCon name res_kind full_kind arity rhs parent
  = mkTyCon name res_kind full_kind arity $
    AlgTyCon { algTcRhs = rhs
             , algTcFlavor = parent }

mkTupleTyCon
  :: Name
  -> Kind
  -> Kind
  -> Arity
  -> DataCon
  -> AlgTyConFlav
  -> TyCon
mkTupleTyCon name res_kind kind arity con parent
  = mkTyCon name res_kind kind arity $
    AlgTyCon { algTcRhs = TupleTyCon { data_con = con }
             , algTcFlavor = parent }

mkSumTyCon
  :: Name
  -> Kind
  -> Kind
  -> Arity
  -> [DataCon]
  -> AlgTyConFlav
  -> TyCon
mkSumTyCon name res_kind kind arity cons parent
  = mkTyCon name res_kind kind arity $
    AlgTyCon { algTcRhs = mkSumTyConRhs cons
             , algTcFlavor = parent }

mkPrimTyCon :: Name -> Kind -> Kind -> Arity -> TyCon
mkPrimTyCon name res_kind kind arity
  = mkTyCon name res_kind kind arity PrimTyCon

mkTcTyCon
  :: Name
  -> Kind
  -> Kind
  -> Arity
  -> [(Name, TcKiVar)]
  -> Bool
  -> TyConFlavor TyCon
  -> TyCon
mkTcTyCon name res_kind full_kind arity scoped_kvs poly flav
  = mkTyCon name res_kind full_kind arity
    $ TcTyCon { tctc_scoped_kvs = scoped_kvs
              , tctc_is_poly = poly
              , tctc_flavor = flav }

isTypeSynonymTyCon :: TyCon -> Bool
isTypeSynonymTyCon (TyCon { tyConDetails = details })
  | SynonymTyCon{} <- details = True
  | otherwise = False
{-# INLINE isTypeSynonymTyCon #-}

tyConMustBeSaturated :: TyCon -> Bool
tyConMustBeSaturated = tcFlavorMustBeSaturated . tyConFlavor

isTupleTyCon :: TyCon -> Bool
isTupleTyCon (TyCon { tyConDetails = details })
  | AlgTyCon { algTcRhs = TupleTyCon {} } <- details = True
  | otherwise = False

{- --------------------------------------------
--      TcTyCon
-------------------------------------------- -}

tcTyConScopedKiVars :: TyCon -> [(Name, TcKiVar)]
tcTyConScopedKiVars tc@(TyCon { tyConDetails = details })
  | TcTyCon { tctc_scoped_kvs = scoped_kvs } <- details = scoped_kvs
  | otherwise = pprPanic "tcTyConScopedKiVars" (ppr tc)

tyConDataCons :: TyCon -> [DataCon]
tyConDataCons tycon = tyConDataCons_maybe tycon `orElse` []

tyConDataCons_maybe :: TyCon -> Maybe [DataCon]
tyConDataCons_maybe (TyCon { tyConDetails = details })
  | AlgTyCon { algTcRhs = rhs } <- details
  = case rhs of
      TupleTyCon { data_con = con } -> Just [con]
      SumTyCon { data_cons = cons } -> Just cons
      _ -> Nothing
tyConDataCons_maybe _ = Nothing      

synTyConDefn_maybe :: TyCon -> Maybe Type
synTyConDefn_maybe (TyCon { tyConDetails = details })
  | SynonymTyCon {synTcRhs = ty} <- details
  = Just ty
  | otherwise
  = Nothing

mkTyConTagMap :: TyCon -> NameEnv ConTag
mkTyConTagMap tycon =
  mkNameEnv $ map getName (tyConDataCons tycon) `zip` [fIRST_TAG..]

{- *********************************************************************
*                                                                      *
            Instance declarations for TyCon
*                                                                      *
********************************************************************* -}

instance Eq TyCon where
  a == b = getUnique a == getUnique b
  a /= b = getUnique a /= getUnique b

instance Uniquable TyCon where
  getUnique tc = tyConUnique tc

instance Outputable TyCon where
  ppr tc = ppr (tyConName tc) <> pp_tc
    where
      pp_tc = getPprStyle $ \ sty ->
              getPprDebug $ \ debug ->
                              if ((debug || dumpStyle sty) && isTcTyCon tc)
                              then text "[tc]"
                              else empty

tyConFlavor :: TyCon -> TyConFlavor TyCon
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

tcFlavorMustBeSaturated :: TyConFlavor tc -> Bool
tcFlavorMustBeSaturated TupleFlavor = False
tcFlavorMustBeSaturated SumFlavor = False
tcFlavorMustBeSaturated DataTypeFlavor = False
tcFlavorMustBeSaturated AbstractTypeFlavor = False
tcFlavorMustBeSaturated TypeFunFlavor = True
tcFlavorMustBeSaturated BuiltInTypeFlavor = False

instance NamedThing TyCon where
  getName = tyConName

instance Data.Data TyCon where
  toConstr _ = abstractConstr "TyCon"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "TyCon"
