{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE MultiWayIf #-}

module CSlash.Types.Var
  ( {-* Var *-}
    Var

    {-* Class methods *-}
  , varName, setVarName
  , varUnique, setVarUnique
  , varType, updateVarType, setVarType
  , varKind, updateVarKind, updateVarKindM, setVarKind
  , swellVar
  , ebbTyVar, ebbTcTyVar, ebbAnyTyVar
  , ebbKiVar, ebbTcKiVar, ebbAnyKiVar
  , ebbId

    {-* TyVar *-}
  , TyVar

    {-* TcTyVar *-}
  , TcTyVar

    {-* AnyTyVar *-}
  , AnyTyVar

    {-* KiVar *-}
  , KiVar

    {-* TcKiVar *-}
  , TcKiVar

    {-* AnyKiVar *-}
  , AnyKiVar

    {-* Id *-}
  , Id
  ) where

import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import {-# SOURCE #-} CSlash.Core.Kind (Kind, MonoKind, pprKind, isCoVarKind)
import {-# SOURCE #-} CSlash.Tc.Utils.TcType
  (TcTyVarDetails, TcKiVarDetails, pprTcTyVarDetails, vanillaSkolemTvUnk, vanillaSkolemKvUnk)
import {-# SOURCE #-} CSlash.Types.Id.Info (IdDetails, IdInfo, pprIdDetails)

{- *********************************************************************
*                                                                      *
                    Var
*                                                                      *
********************************************************************* -}

data Var
  = TyVar
    { _varName :: !Name
    , _realUnique :: {-# UNPACK #-} !Unique
    , _varKind :: MonoKind
    }
  | TcTyVar -- for type inference
    { _varName :: !Name
    , _realUnique :: {-# UNPACK #-} !Unique
    , _varKind :: MonoKind
    , _tc_tv_details :: TcTyVarDetails
    }
  | KiVar
    { _varName :: !Name
    , _realUnique :: {-# UNPACK #-} !Unique
    }
  | TcKiVar -- for kind inference
    { _varName :: !Name
    , _realUnique :: {-# UNPACK #-} !Unique
    , _tc_kv_details :: TcKiVarDetails
    }
  | Id
    { _varName :: !Name
    , _realUnique :: {-# UNPACK #-} !Unique
    , _varType :: Type
    , _idScope :: IdScope
    , _id_details :: IdDetails
    , _id_info :: IdInfo
    }

data IdScope
  = GlobalId
  | LocalId ExportFlag

data ExportFlag
  = NotExported
  | Exported

instance Outputable Var where
  ppr var = 
    getPprDebug $ \ debug ->
    getPprStyle $ \ sty ->
    let ppr_var = case var of
          (TyVar {}) | debug -> brackets (text "tv")
          (KiVar {}) | debug -> brackets (text "kv")
          (TcTyVar { _tc_tv_details = d })
            | dumpStyle sty || debug
            -> brackets (pprTcTyVarDetails d)
          (TcKiVar { _tc_kv_details = d })
            | dumpStyle sty || debug
            -> brackets (pprTcKiVarDetails d)
          (Id { _idScope = s, _id_details = d })
            | debug
            -> brackets (ppr_id_scope s <> pprIdDetails d)
        ppr_tyki = case var of
          (TyVar { _varKind = ki }) -> char ' ' <> colon <+> ppr ki
          (TcTyVar { _varKind = ki }) -> char ' ' <> colon <+> ppr ki
          (Id { _varType = ty }) -> char ' ' <> colon <+> ppr ty
          _ -> empty
          
    in if debug
       then parens (ppr (_varName var) <+> ppr_var <> ppr_tyki)
       else ppr (_varName var) <> ppr_var
    
ppr_id_scope :: IdScope -> SDoc
ppr_id_scope GlobalId = text "gid"
ppr_id_scope (LocalId Exported) = text "lidx"
ppr_id_scope (LocalId NotExported) = text "lid"

instance NamedThing Var where
  getName = varName

instance Uniquable Var where
  getUnique = realUnique

instance Eq Var where
  a == b = realUnique a == realUnique b

instance Ord Var where
  a <= b = getKey (realUnique a) <= getKey (realUnique b)
  a < b = getKey (realUnique a) < getKey (realUnique b)
  a >= b = getKey (realUnique a) >= getKey (realUnique b)
  a > b = getKey (realUnique a) > getKey (realUnique b)
  a `compare` b = a `nonDetCmpVar` b
    where
      nonDetCmpVar :: Var -> Var -> Ordering
      nonDetCmpVar a b = varUnique a `nonDetCmpUnique` varUnique b

instance Data Var where
  toConstr _ = abstractConstr "Var"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "Var"

instance HasOccName Var where
  occName = nameOccName . varName

{- *********************************************************************
*                                                                      *
                    Utility classes
*                                                                      *
********************************************************************* -}

class VarHasName v where
  varName :: v -> Name
  setVarName :: v -> Name -> v

instance VarHasName Var where
  varName = _varName
  setVarName var new_name = var { _realUnique = getUnique new_name
                                , _varName = new_name }

class VarHasUnique v where
  varUnique :: v -> Unique
  setVarUnique :: v -> Unique -> v

instance VarHasUnique Var where
  varUnique = _realUnique
  setVarUnique var uniq = var { _realUnique = uniq
                              , _varName = setNameUnique (_varName var) uniq }

class VarHasType v where
  varType :: v -> Type
  updateVarType :: (Type -> Type) -> v -> v
  setVarType :: v -> Type -> v

class VarHasKind v where
  varKind :: v -> MonoKind
  updateVarKind :: (MonoKind -> MonoKind) -> v -> v
  updateVarKindM :: Monad m => (MonoKind -> m MonoKind) -> v -> m v
  setVarKind :: v -> MonoKind -> v

class VarHasTcDetails v d | v -> d where
  tcVarDetails :: v -> d

class VarCanSetTcDetails v d | v -> d where
  setTcVarDetails :: v -> d -> v

class SwellVar v1 v2 | v1 -> v2 where
  swellVar :: v1 -> v2

class EbbTyVar v where
  ebbTyVar :: v -> Maybe TyVar

instance EbbTyVar Var where
  ebbTyVar tv@(TyVar {}) = Just $ TyVar tv
  ebbTyVar _ = Nothing

class EbbTcTyVar v where
  ebbTcTyVar :: v -> Maybe TcTyVar

instance EbbTcTyVar Var where
  ebbTcTyVar tv@(TcTyVar {}) = Just $ TcTyVar tv
  ebbTcTyVar _ = Nothing

class EbbAnyTyVar v where
  ebbAnyTyVar :: v -> Maybe AnyTyVar

instance EbbAnyTyVar Var where
  ebbAnyTyVar tv@(TyVar {}) = Just $ AnyTyVar tv
  ebbAnyTyVar tv@(TcTyVar {}) = Just $ AnyTyVar tv
  ebbAnyTyVar _ = Nothing

class EbbKiVar v where
  ebbKiVar :: v -> Maybe KiVar

instance EbbKiVar Var where
  ebbKiVar kv@(KiVar {}) = Just $ KiVar kv
  ebbKiVar _ = Nothing

class EbbTcKiVar v where
  ebbTcKiVar :: v -> Maybe TcKiVar

instance EbbTcKiVar Var where
  ebbTcKiVar kv@(TcKiVar {}) = Just $ TcKiVar kv
  ebbTcKiVar _ = Nothing

class EbbAnyKiVar v where
  ebbAnyKiVar :: v -> Maybe AnyKiVar

instance EbbAnyKiVar Var where
  ebbAnyKiVar kv@(KiVar {}) = Just $ AnyKiVar kv
  ebbAnyKiVar kv@(TcKiVar {}) = Just $ AnyKiVar kv
  ebbAnyKiVar _ = Nothing

class EbbId v where
  ebbId :: v -> Maybe Id

instance EbbId Var where
  ebbId id@(Id {}) = Just $ Id id
  ebbId _ = Nothing

{- *********************************************************************
*                                                                      *
                    TyVar
*                                                                      *
********************************************************************* -}

newtype TyVar = TyVar Var
  deriving ( Outputable, NamedThing, Uniquable, Eq, Ord, Data, HasOccName
           , VarHasName, VarHasUnique)

instance VarHasKind TyVar where
  varKind (TyVar { _varKind = ki }) = ki
  varKind other = pprPanic "Bad TyVar" (ppr other)

  updateVarKind upd var@(TyVar {}) = var { _varKind = upd (_varKind var) }
  updateVarKind _ other = pprPanic "Bad TyVar" (ppr other)

instance SwellVar TyVar AnyTyVar where
  swellVar (TyVar v) = AnyTyVar v

mkTyVar :: Name -> MonoKind -> TyVar
mkTyVar name kind = TyVar (TyVar { _varName = name
                                 , _realUnique = nameUnique name
                                 , _varKind = kind })

{- *********************************************************************
*                                                                      *
                    TcyTyVar
*                                                                      *
********************************************************************* -}

newtype TcTyVar = TcTyVar Var
  deriving ( Outputable, NamedThing, Uniquable, Eq, Ord, Data, HasOccName
           , VarHasName, VarHasUnique)
  
instance VarHasKind TcTyVar where
  varKind (TcTyVar (TcTyVar { _varKind = ki })) = ki
  varKind (TcTyVar other) = pprPanic "Bad TcTyVar" (ppr other)

  updateVarKind upd (AnyTyVar var@(TyVar {})) = AnyTyVar (var { _varKind = upd (_varKind var) })
  updateVarKind upd (AnyTyVar var@(TcTyVar {})) = AnyTyVar (var { _varKind = upd (_varKind var) })
  updateVarKind _ (AnyTyVar other) = pprPanic "Bad TcTyVar" (ppr other)

instance VarHasTcDetails TcTyVar TcTyVarDetails where
  tcVarDetails (TcTyVar (TcTyVar { _tc_tv_details = details })) = details
  tcVarDetails (TcTyVar other) = pprPanic "Bad TcKiVar" (ppr other)

instance VarCanSetTcDetails TcTyVar TcTyVarDetails where
  setTcVarDetails (TcTyVar v) d = TcTyVar (v { _tc_tv_details = d })

instance SwellVar TcTyVar AnyTyVar where
  swellVar (TcTyVar var) = AnyTyVar var

mkTcTyVar :: Name -> MonoKind -> TcTyVarDetails -> TcTyVar
mkTcTyVar name kind details = TcTyVar (TcTyVar { _varName = name
                                               , _realUnique = nameUnique name
                                               , _varKind = kind
                                               , _tc_kv_details = details })

{- *********************************************************************
*                                                                      *
                    AnyTyVar
*                                                                      *
********************************************************************* -}

newtype AnyTyVar = AnyTyVar Var
  deriving ( Outputable, NamedThing, Uniquable, Eq, Ord, Data, HasOccName
           , VarHasName, VarHasUnique)

instance VarHasKind AnyTyVar where
  varKind (AnyTyVar (TyVar { _varKind = ki })) = ki
  varKind (AnyTyVar (TcTyVar { _varKind = ki })) = ki
  varKind (AnyTyVar other) = pprPanic "Bad AnyTyVar" (ppr other)

  updateVarKind upd (AnyTyVar var@(TyVar {})) = AnyTyVar (var { _varKind = upd (_varKind var) })
  updateVarKind upd (AnyTyVar var@(TcTyVar {})) = AnyTyVar (var { _varKind = upd (_varKind var) })
  updateVarKind _ (AnyTyVar other) = pprPanic "Bad AnyTyVar" (ppr other)

instance VarHasTcDetails AnyTyVar TcTyVarDetails where
  tcVarDetails (AnyTyVar (TcTyVar { _tc_tv_details = details })) = details
  tcVarDetails (AnyTyVar (TyVar {})) = vanillaSkolemTvUnk
  tcVarDetails (AnyTyVar other) = pprPanic "Bad TcKiVar" (ppr other)

instance SwellVar AnyTyVar Var where
  swellVar (AnyTyVar var) = var

instance EbbTyVar AnyTyVar where
  ebbTyVar (AnyTyVar v@(TyVar {})) = Just $ TyVar v
  ebbTyVar _ = Nothing

instance EbbTcTyVar AnyTyVar where
  ebbTcTyVar (AnyTyVar v@(TcTyVar {})) = Just $ TcTyVar v
  ebbTcTyVar _ = Nothing

{- *********************************************************************
*                                                                      *
                    KiVar
*                                                                      *
********************************************************************* -}

newtype KiVar = KiVar Var
  deriving ( Outputable, NamedThing, Uniquable, Eq, Ord, Data, HasOccName
           , VarHasName, VarHasUnique)

instance SwellVar KiVar AnyKiVar where
  swellVar (KiVar var) = AnyKiVar var

mkKiVar :: Name -> KiVar
mkKiVar name = KiVar (KiVar { _varName = name, _realUnique = nameUnique name })

{- *********************************************************************
*                                                                      *
                    TcKiVar
*                                                                      *
********************************************************************* -}

newtype TcKiVar = TcKiVar Var
  deriving ( Outputable, NamedThing, Uniquable, Eq, Ord, Data, HasOccName
           , VarHasName, VarHasUnique)

instance VarHasTcDetails TcKiVar TcKiVarDetails where
  tcVarDetails (TcKiVar (TcKiVar { _tc_kv_details = details })) = details
  tcVarDetails (TcKiVar other) = pprPanic "Bad TcKiVar" (ppr other)

instance VarCanSetTcDetails TcKiVar TcKiVarDetails where
  setTcVarDetails (TcKiVar v) d = TcKiVar (v { _tc_kv_details = d })

instance SwellVar TcKiVar AnyKiVar where
  swellVar (TcKiVar var) = AnyKiVar var

mkTcKiVar :: Name -> TcKiVarDetails -> TcKiVar
mkTcKiVar name details = TcKiVar (TcKiVar { _varName = name
                                          , _realUnique = nameUnique name
                                          , _tc_kv_details = details })

{- *********************************************************************
*                                                                      *
                    AnyKiVar
*                                                                      *
********************************************************************* -}

newtype AnyKiVar = AnyKiVar Var
  deriving ( Outputable, NamedThing, Uniquable, Eq, Ord, Data, HasOccName
           , VarHasName, VarHasUnique)

instance VarHasTcDetails AnyKiVar TcKiVarDetails where
  tcVarDetails (TcKiVar (TcKiVar { _tc_kv_details = details })) = details
  tcVarDetails (TcKiVar (KiVar {})) = vanillaSkolemKvUnk
  tcVarDetails (TcKiVar other) = pprPanic "Bad TcKiVar" (ppr other)

instance SwellVar AnyKiVar Var where
  swellVar (AnyKiVar var) = var

instance EbbKiVar AnyKiVar where
  ebbKiVar (AnyKiVar v@(KiVar {})) = Just $ KiVar v
  ebbKiVar _ = Nothing

instance EbbTcKiVar AnyKiVar where
  ebbTcKiVar (AnyKiVar v@(TcKiVar {})) = Just $ TcKiVar v
  ebbTcKiVar _ = Nothing

{- *********************************************************************
*                                                                      *
                    Id
*                                                                      *
********************************************************************* -}

newtype Id = Id Var
  deriving ( Outputable, NamedThing, Uniquable, Eq, Ord, Data, HasOccName
           , VarHasName, VarHasUnique)
    
instance VarHasType Id where
  varType (Id { varType = ty }) = ty
  varType other = pprPanic "Bad Id" (ppr other)

instance SwellVar Id Var where
  swellVar (Id var) = var
