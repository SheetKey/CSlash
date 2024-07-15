module CSlash.Core.TyCon where

import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)

import CSlash.Core.Kind (Kind)

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

type TyConBinder = VarBndr TypeVar TyConBndrVis

data TyConBndrVis
  = NamedTCB ForAllTyFlag
  | AnonTCB

instance Outputable TyConBndrVis where
  ppr (NamedTCB flag) = ppr flag
  ppr AnonTCB         = text "AnonTCB"

instance OutputableBndr tv => Outputable (VarBndr tv TyConBndrVis) where
  ppr (Bndr v bi) = ppr bi <+> parens (pprBndr LetBind v)

instance Binary TyConBndrVis where
  put_ bh AnonTCB        = do { putByte bh 0 }
  put_ bh (NamedTCB vis) = do { putByte bh 1; put_ bh vis }

  get bh = do { h <- getByte bh
              ; case h of
                  0 -> return AnonTCB
                  _ -> do { vis <- get bh; return (NamedTCB vis) } }

{- *********************************************************************
*                                                                      *
               The TyCon type
*                                                                      *
********************************************************************* -}

data TyCon = TyCon
  { tyConUnique :: !Unique
  , tyConName :: !Name
  , tyConBinders :: [TyConBinder]
  , tyConResKind :: Kind
  , tyConHasClosedResKind :: Bool
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
    , algTcFields :: FieldLabelEnv
    , algTcFlavor :: AlgTyConFlav
    }
  | SynonymTyCon
    { synTcRhs :: Type
    , synIsTau :: Bool
    , synIsForgetful :: Bool
    , synIsConcrete :: Bool
    }
  | PrimTyCon
    { primRepName :: TyConRepName }
  | TcTyCon -- used during type checking only
    { tctc_scoped_tvs :: [(Name, TcTyVar)]
    , tctc_is_poly :: Bool
    , tctc_flavor :: TyConFlavor TyCon
    }

data AlgTyConRhs
  = AbstractTyCon
  | TupleTyCon
    { data_con :: DataCon
    , tup_sort :: TupleSort
    }
  | SumTyCon
    { data_cons :: [DataCon]
    , data_cons_size :: Int
    }

data AlgTyConFlav
  = VanillaAlgTyCon TyConRepName
  | AlgSumTyCon

instance Outputable AlgTyConFlav where
  ppr (VanillaAlgTyCon {}) = text "Vanilla ADT"
  ppr (AlgSumTyCon {}) = text "Sum"

************************************************************************
*                                                                      *
                 TyConRepName
*                                                                      *
********************************************************************* -}

type TyConRepName = Name


