{-# LANGUAGE FlexibleInstances #-}

module CSlash.Core.TyCon where

import Prelude hiding ((<>))

import {-# SOURCE #-} CSlash.Core.Type.Rep (Type, mkNakedTyConTy)
import {-# SOURCE #-} CSlash.Core.DataCon (DataCon, dataConFullSig)

import CSlash.Core.Kind

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

    go [Bndr tv _] (FunKd _ arg_kd _)
      | isTyVar tv = varKind tv == arg_kd
    go ((Bndr tv _):bndrs) (FunKd _ arg_kd res_kd)
      | isTyVar tv = varKind tv == arg_kd && go bndrs res_kd
    go _ _ = panic "verifyTyConKind_go"

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
  , tyConBinders :: [TyConBinder]
  , tyConResKind :: Kind -- Lin, Aff, Unr, or a variable
  -- , tyConHasClosedResKind :: Bool
  , tyConTyVars :: [TypeVar]
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
    { tctc_scoped_tvs :: [(Name, TcTyVar)]
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
    is_enum_con con
      = let (_univ_tvs, arg_tys, _res) = dataConFullSig con
        in null arg_tys
      
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

mkTyCon :: Name -> [TyConBinder] -> Kind -> Kind -> TyConDetails -> TyCon
mkTyCon name binders res_kind kind details
  = tc
  where
    tc = TyCon { tyConUnique = nameUnique name
               , tyConName = name
               , tyConBinders = binders
               , tyConTyVars = binderVars binders
               , tyConResKind = res_kind
               , tyConKind = verifyTyConKind binders kind
               , tyConArity = length binders
               , tyConNullaryTy = mkNakedTyConTy tc
               , tyConDetails = details
               }

mkAlgTyCon
  :: Name
  -> [TyConBinder]
  -> Kind
  -> Kind
  -> AlgTyConRhs
  -> AlgTyConFlav
  -> TyCon
mkAlgTyCon name binders res_kind kind rhs parent
  = mkTyCon name binders res_kind kind $
    AlgTyCon { algTcRhs = rhs
             , algTcFlavor = parent }

mkTupleTyCon
  :: Name
  -> [TyConBinder]
  -> Kind
  -> Kind
  -> DataCon
  -> AlgTyConFlav
  -> TyCon
mkTupleTyCon name binders res_kind kind con parent
  = mkTyCon name binders res_kind kind $
    AlgTyCon { algTcRhs = TupleTyCon { data_con = con }
             , algTcFlavor = parent }

mkSumTyCon
  :: Name
  -> [TyConBinder]
  -> Kind
  -> Kind
  -> [DataCon]
  -> AlgTyConFlav
  -> TyCon
mkSumTyCon name binders res_kind kind cons parent
  = mkTyCon name binders res_kind kind $
    AlgTyCon { algTcRhs = mkSumTyConRhs cons
             , algTcFlavor = parent }

mkPrimTyCon :: Name -> [TyConBinder] -> Kind -> Kind -> TyCon
mkPrimTyCon name binders res_kind kind
  = mkTyCon name binders res_kind kind PrimTyCon

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

synTyConDefn_maybe :: TyCon -> Maybe ([TypeVar], Type)
synTyConDefn_maybe (TyCon { tyConTyVars = tyvars, tyConDetails = details })
  | SynonymTyCon {synTcRhs = ty} <- details
  = Just (tyvars, ty)
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

instance NamedThing TyCon where
  getName = tyConName

instance Data.Data TyCon where
  toConstr _ = abstractConstr "TyCon"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "TyCon"
