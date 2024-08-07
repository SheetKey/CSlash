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

-- BAD
-- mkTyConKind :: [TyConBinder] -> Kind -> Kind
-- mkTyConKind bndrs res_kind = foldr mk res_kind bndrs
--   where
--     mk :: TyConBinder -> Kind -> Kind
--     mk (Bndr tv vis) k = case tv of
--                            TvVar { varKind = arg_k }
--                              | isCKind arg_k
--                              , isCKind k
--                                = FunKd FKF_C_C arg_k k
--                              | isCKind arg_k
--                                = FunKd FKF_C_K arg_k k
--                              | isCKind k
--                                = panic "mkTyConKind"
--                              | otherwise
--                                = FunKd FKF_K_K arg_k k
--                            _ -> panic "mkTyConKind"

{- *********************************************************************
*                                                                      *
               The TyCon type
*                                                                      *
********************************************************************* -}

data TyCon = TyCon
  { tyConUnique :: !Unique
  , tyConName :: !Name
  , tyConBinders :: [TyConBinder]
  -- , tyConResKind :: Kind       -- This doesn't make sense due to kind constraints:
                                  -- The result kind may depend on the kinds of
                                  -- the type arguments:
                                  -- a tuple containing a linear value should have
                                  -- a linear kind regardless of the other fields.
                                  -- To have kind polymorphism, this is not statically known.
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

mkTyCon :: Name -> [TyConBinder] -> Kind -> TyConDetails -> TyCon
mkTyCon name binders kind details
  = tc
  where
    tc = TyCon { tyConUnique = nameUnique name
               , tyConName = name
               , tyConBinders = binders
               , tyConTyVars = binderVars binders
               , tyConKind = verifyTyConKind binders kind
               , tyConArity = length binders
               , tyConNullaryTy = mkNakedTyConTy tc
               , tyConDetails = details
               }

mkAlgTyCon
  :: Name
  -> [TyConBinder]
  -> Kind
  -> AlgTyConRhs
  -> AlgTyConFlav
  -> TyCon
mkAlgTyCon name binders kind rhs parent
  = mkTyCon name binders kind $
    AlgTyCon { algTcRhs = rhs
             , algTcFlavor = parent }

mkTupleTyCon
  :: Name
  -> [TyConBinder]
  -> Kind
  -> DataCon
  -> AlgTyConFlav
  -> TyCon
mkTupleTyCon name binders kind con parent
  = mkTyCon name binders kind $
    AlgTyCon { algTcRhs = TupleTyCon { data_con = con }
             , algTcFlavor = parent }

mkSumTyCon
  :: Name
  -> [TyConBinder]
  -> Kind
  -> [DataCon]
  -> AlgTyConFlav
  -> TyCon
mkSumTyCon name binders kind cons parent
  = mkTyCon name binders kind $
    AlgTyCon { algTcRhs = mkSumTyConRhs cons
             , algTcFlavor = parent }

mkPrimTyCon :: Name -> [TyConBinder] -> Kind -> TyCon
mkPrimTyCon name binders kind
  = mkTyCon name binders kind PrimTyCon

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
