{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}

module CSlash.Types.Var.Id where

import Prelude hiding ((<>))

import CSlash.Core hiding (Id)

import {-# SOURCE #-} CSlash.Core.Type (typeKind)
import {-# SOURCE #-} CSlash.Core.Type.Rep (Type, PredType)
import {-# SOURCE #-} CSlash.Core.Kind (Kind, MonoKind)
import {-# SOURCE #-} CSlash.Tc.Utils.TcType (TcVarDetails, pprTcVarDetails)
import {-# SOURCE #-} CSlash.Types.Var.Id.Info (IdDetails, IdInfo, pprIdDetails)
import {-# SOURCE #-} CSlash.Core.DataCon
import {-# SOURCE #-} CSlash.Core.Subst (fromZkType)
import {-# SOURCE #-} CSlash.Core.Predicate (isTyCoVarType)
import {-# SOURCE #-} CSlash.Core (Unfolding(..))

import CSlash.Cs.Pass

import CSlash.Types.Var.Class
import CSlash.Types.Var.Id.Info

import CSlash.Types.Name hiding (varName)
import CSlash.Types.Unique
import CSlash.Types.Unique.Supply
import CSlash.Types.Basic
import CSlash.Types.SrcLoc
import CSlash.Types.Demand
import CSlash.Data.FastString

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Trace

import Data.Data

data Id p
  = Id
    { id_name :: !Name
    , id_real_unique :: {-# UNPACK #-} !Unique
    , id_type :: Type p
    , id_scope :: IdScope
    , id_details :: IdDetails
    , id_info :: IdInfo
    }

data IdScope
  = GlobalId
  | LocalId ExportFlag

data ExportFlag
  = NotExported
  | Exported

instance IsVar (Id p) where
  varName = id_name
  setVarName id name = id { id_name = name }

  varUnique = id_real_unique
  setVarUnique id unique = id { id_real_unique = unique }

  isTcVar _ = False

instance IsPass p => Outputable (Id (CsPass p)) where
  ppr Id {..} = docWithStyle ppr_code ppr_normal
    where
      ppr_code = ppr id_name
      ppr_normal sty = getPprDebug $ \debug ->
        let ppr_var | debug = brackets (ppr_id_scope id_scope <> pprIdDetails id_details)
                    | otherwise = empty
        in if debug
           then parens (ppr id_name <+> ppr_var <+> colon <+> ppr id_type)
           else ppr id_name <> ppr_var

ppr_id_scope :: IdScope -> SDoc
ppr_id_scope GlobalId = text "gid"
ppr_id_scope (LocalId Exported) = text "lidx"
ppr_id_scope (LocalId NotExported) = text "lid"

instance (Typeable p) => Data (Id p) where
  toConstr _ = abstractConstr "Id"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "Id"

instance Eq (Id p) where
  a == b = id_real_unique a == id_real_unique b

instance Ord (Id p) where
  a <= b = getKey (id_real_unique a) <= getKey (id_real_unique b)
  a < b = getKey (id_real_unique a) < getKey (id_real_unique b)
  a >= b = getKey (id_real_unique a) >= getKey (id_real_unique b)
  a > b = getKey (id_real_unique a) > getKey (id_real_unique b)
  a `compare` b = id_real_unique a `nonDetCmpUnique` id_real_unique b

instance NamedThing (Id p) where
  getName = id_name

instance Uniquable (Id p) where
  getUnique = id_real_unique

instance VarHasType (Id p) p where
  varType = id_type
  setVarType id ty = id { id_type = ty }
  updateVarType f id@(Id { id_type = ty }) = id { id_type = f ty }
  updateVarTypeM f id@(Id { id_type = ty }) = do
    ty' <- f ty
    return id { id_type = ty' }

mk_id :: Name -> Type p -> IdScope -> IdDetails -> IdInfo -> Id p
mk_id name ty scope details info = Id { id_name = name
                                      , id_real_unique = nameUnique name
                                      , id_type = ty
                                      , id_scope = scope
                                      , id_details = details
                                      , id_info = info }

mkGlobalId :: IdDetails -> Name -> Type p -> IdInfo -> Id p
mkGlobalId details name ty info = mk_id name ty GlobalId details info

mkLocalId :: Name -> Type p -> Id p
mkLocalId name ty = mkLocalIdWithInfo name ty vanillaIdInfo

mkLocalIdWithInfo :: Name -> Type p -> IdInfo -> Id p
mkLocalIdWithInfo name ty info = mk_id name ty (LocalId NotExported) VanillaId info

mkLocalIdWithDetailsAndInfo :: IdDetails -> Name -> Type p -> IdInfo -> Id p
mkLocalIdWithDetailsAndInfo d n t i
  = mk_id n t (LocalId NotExported) d i

mkSysLocal :: HasPass p p' => FastString -> Unique -> Type p -> Id p
mkSysLocal fs uniq ty = assert (not (isTyCoVarType ty)) $
                        mkLocalId (mkSystemVarName uniq fs) ty

mkSysLocalM :: (MonadUnique m, HasPass p p') => FastString -> Type p -> m (Id p)
mkSysLocalM fs ty = getUniqueM >>= \uniq -> return $ mkSysLocal fs uniq ty

mkUserLocal :: HasPass p p' => OccName -> Unique -> Type p -> SrcSpan -> Id p
mkUserLocal occ uniq ty loc = assert (not (isTyCoVarType ty)) $
                              mkLocalId (mkInternalName uniq occ loc) ty

idInfo :: Id p -> IdInfo
idInfo = id_info

idDetails :: Id p -> IdDetails
idDetails = id_details

idOccInfo :: Id p -> OccInfo
idOccInfo id = occInfo (idInfo id)

zapIdOccInfo :: Id p -> Id p
zapIdOccInfo b = b `setIdOccInfo` noOccInfo

isDeadBinder :: Id p -> Bool
isDeadBinder bndr = isDeadOcc (idOccInfo bndr)

idKind :: HasPass p pass => Id p -> Kind p
idKind = typeKind . varType

changeIdType :: (Type p -> Type p') -> Id p -> Id p'
changeIdType f (Id { id_type = ty, .. }) = Id { id_type = f ty, .. }

changeIdTypeM :: Monad m => (Type p -> m (Type p')) -> Id p -> m (Id p')
changeIdTypeM f (Id { id_type = ty, .. }) = do
  ty' <- f ty
  return $ Id { id_type = ty', .. }  

fromZkId :: HasPass p pass => Id Zk -> Id p
fromZkId = changeIdType fromZkType

setIdExported :: Id p -> Id p
setIdExported id@(Id { id_scope = LocalId {} }) = id { id_scope = LocalId Exported }
setIdExported id@(Id { id_scope = GlobalId }) = id

localizeId :: Id p -> Id p
localizeId id
  | isLocalId id && isInternalName (varName id)
  = id
  | otherwise
  = mk_id (localiseName $ varName id) (varType id) (LocalId NotExported) (idDetails id) (idInfo id)

lazySetIdInfo :: Id p -> IdInfo -> Id p
lazySetIdInfo id info = id { id_info = info }

setIdDetails :: Id p -> IdDetails -> Id p
setIdDetails id details = id { id_details = details }

setIdInfo :: Id p -> IdInfo -> Id p
setIdInfo id info = info `seq` (lazySetIdInfo id info)

modifyIdInfo :: (IdInfo -> IdInfo) -> Id p -> Id p
modifyIdInfo fn id = setIdInfo id (fn (idInfo id))

maybeModifyIdInfo :: Maybe IdInfo -> Id p -> Id p
maybeModifyIdInfo (Just new_info) id = lazySetIdInfo id new_info
maybeModifyIdInfo Nothing id = id

{- *********************************************************************
*                                                                      *
            Special Ids
*                                                                      *
********************************************************************* -}

isDataConId :: Id p -> Bool
isDataConId id = case idDetails id of
                   DataConId {} -> True
                   _ -> False

isDataConId_maybe :: Id p -> Maybe (DataCon Zk)
isDataConId_maybe id = case idDetails id of
                         DataConId con -> Just con
                         _ -> Nothing

isGlobalId :: Id p -> Bool
isGlobalId (Id {id_scope = GlobalId }) = True
isGlobalId _ = False

isExportedId :: Id p -> Bool
isExportedId (Id { id_scope = GlobalId }) = True
isExportedId (Id { id_scope = LocalId Exported }) = True
isExportedId _ = False

isLocalId :: Id p -> Bool
isLocalId (Id { id_scope = LocalId _ }) = True
isLocalId _ = False

isLocalId_maybe :: Id p -> Maybe ExportFlag
isLocalId_maybe Id{ id_scope = LocalId ef } = Just ef
isLocalId_maybe _ = Nothing

isJoinId :: Id p -> Bool
isJoinId id = case idDetails id of
  JoinId _ -> True
  _ -> False

idJoinPointHood :: Id p -> JoinPointHood
idJoinPointHood id = case idDetails id of
                       JoinId arity -> JoinPoint arity
                       _ -> NotJoinPoint

hasNoBinding :: Id p -> Bool
hasNoBinding id = case idDetails id of
  DataConId dc -> panic "isTupleDataCon dc"
                  --  || isSumDataCon dc
  VanillaId -> rest
  TickBoxOpId _ -> rest
  JoinId _ -> rest 
  where
    rest = isCompulsoryUnfolding (realIdUnfolding id)

zapJoinId :: Id p -> Id p
zapJoinId jid
  | isJoinId jid = zapIdTailCallInfo (newIdDetails `seq` jid `setIdDetails` newIdDetails)
  | otherwise = jid
  where
    newIdDetails = case idDetails jid of
      JoinId _ -> VanillaId -- TODO: should we add 'WorkerLikeId'??
      _ -> panic "impossible"

asJoinId_maybe :: HasPass p p' => Id p -> JoinPointHood -> Id p
asJoinId_maybe id (JoinPoint arity) = asJoinId id arity
asJoinId_maybe id NotJoinPoint = zapJoinId id

{- *********************************************************************
*                                                                      *
            IdInfo stuff
*                                                                      *
********************************************************************* -}

---------------------------------
-- ARITY

idArity :: Id p -> Arity
idArity id = arityInfo (idInfo id)

setIdArity :: Id p -> Arity -> Id p
setIdArity id arity = modifyIdInfo (`setArityInfo` arity) id

isDeadEndId :: Id p -> Bool
isDeadEndId id = isDeadEndSig (idDmdSig id)

idDmdSig :: Id p -> DmdSig
idDmdSig id = dmdSigInfo (idInfo id)

setIdDmdSig :: Id p -> DmdSig -> Id p
setIdDmdSig id sig = modifyIdInfo (`setDmdSigInfo` sig) id

---------------------------------
-- UNFOLDING

idUnfolding :: Id p -> Unfolding
idUnfolding id = unfoldingInfo (idInfo id)

noUnfoldingFun :: Id p -> Unfolding
noUnfoldingFun _ = noUnfolding

alwaysActiveUnfoldingFun :: IdUnfoldingFun
alwaysActiveUnfoldingFun id
  | isAlwaysActive (idInlineActivation id) = idUnfolding id
  | otherwise = noUnfolding

whenActiveUnfoldingFun :: (Activation -> Bool) -> IdUnfoldingFun
whenActiveUnfoldingFun is_active id
  | is_active (idInlineActivation id) = idUnfolding id
  | otherwise = NoUnfolding

realIdUnfolding :: Id p -> Unfolding
realIdUnfolding id = realUnfoldingInfo (idInfo id)

setIdUnfolding :: Id p -> Unfolding -> Id p
setIdUnfolding id unfolding = modifyIdInfo (`setUnfoldingInfo` unfolding) id

idDemandInfo :: Id p -> Demand
idDemandInfo id = demandInfo (idInfo id)

setIdDemandInfo :: Id p -> Demand -> Id p
setIdDemandInfo id dmd = modifyIdInfo (`setDemandInfo` dmd) id

setCaseBndrEvald :: Id p -> Id p
setCaseBndrEvald id = id `setIdUnfolding` evaldUnfolding

zapIdUnfolding :: Id p -> Id p
zapIdUnfolding v
  | hasSomeUnfolding (idUnfolding v) = setIdUnfolding v noUnfolding
  | otherwise = v

---------------------------------
-- SPECIALIZATION

idSpecialization :: Id p -> RuleInfo
idSpecialization id = ruleInfo (idInfo id)

idCoreRules :: Id p -> [CoreRule]
idCoreRules id = ruleInfoRules (idSpecialization id)

setIdSpecialization :: Id p -> RuleInfo -> Id p
setIdSpecialization id spec_info = modifyIdInfo (`setRuleInfo` spec_info) id

---------------------------------
-- Occurrence INFO

setIdOccInfo :: Id p -> OccInfo -> Id p
setIdOccInfo id occ_info = modifyIdInfo (`setOccInfo` occ_info) id

---------------------------------
-- INLINING

idInlinePragma :: Id p -> InlinePragma
idInlinePragma id = inlinePragInfo (idInfo id)

setInlinePragma :: Id p -> InlinePragma -> Id p
setInlinePragma id prag = modifyIdInfo (`setInlinePragInfo` prag) id

idRuleMatchInfo :: Id p -> RuleMatchInfo
idRuleMatchInfo id = inlinePragmaRuleMatchInfo (idInlinePragma id)

isConLikeId :: Id p -> Bool
isConLikeId id = isConLike (idRuleMatchInfo id)

idInlineActivation :: Id p -> Activation
idInlineActivation id = inlinePragmaActivation (idInlinePragma id)

---------------------------------
-- ONE-SHOT LAMBDAS

idOneShotInfo :: Id p -> OneShotInfo
idOneShotInfo id = oneShotInfo (idInfo id)

setOneShotLambda :: Id p -> Id p
setOneShotLambda id = modifyIdInfo (`setOneShotInfo` OneShotLam) id

setIdOneShotInfo :: Id p -> OneShotInfo -> Id p
setIdOneShotInfo id one_shot = modifyIdInfo (`setOneShotInfo` one_shot) id

updOneShotInfo :: Id p -> OneShotInfo -> Id p
updOneShotInfo id one_shot
  | OneShotLam <- one_shot
  , NoOneShotInfo <- idOneShotInfo id
  = setIdOneShotInfo id OneShotLam
  | otherwise
  = id

zapInfo :: (IdInfo -> Maybe IdInfo) -> Id p -> Id p
zapInfo zapper id = maybeModifyIdInfo (zapper (idInfo id)) id

zapFragileIdInfo :: Id p -> Id p
zapFragileIdInfo = zapInfo zapFragileInfo

zapIdTailCallInfo :: Id p -> Id p
zapIdTailCallInfo = zapInfo zapTailCallInfo

floatifyIdDemandInfo :: Id p -> Id p
floatifyIdDemandInfo = zapInfo floatifyDemandInfo

transferPolyIdInfo
  :: CoreId
  -> [(CoreBndr, a)]
  -> CoreId
  -> CoreId
transferPolyIdInfo old_id abstract_wrt new_id
  = modifyIdInfo transfer new_id
  where
    arity_increase = count (isRuntimeVar . fst) abstract_wrt

    old_info = idInfo old_id
    old_arity = arityInfo old_info
    old_inline_prag = inlinePragInfo old_info
    old_occ_info = occInfo old_info
    new_arity = old_arity + arity_increase
    new_occ_info = zapOccTailCallInfo old_occ_info

    old_strictness = dmdSigInfo old_info
    new_strictness = prependArgsDmdSig arity_increase old_strictness

    transfer new_info = new_info `setArityInfo` new_arity
                                 `setInlinePragInfo` old_inline_prag
                                 `setOccInfo` new_occ_info
                                 `setDmdSigInfo` new_strictness

{- *********************************************************************
*                                                                      *
              Join variables
*                                                                      *
********************************************************************* -}

asJoinId :: HasPass p p' => Id p -> JoinArity -> Id p
asJoinId id arity = warnPprTrace (not (isLocalId id))
                    "global id being marked as a join var" (ppr id) $
                    warnPprTrace (not (is_vanilla_or_join id))
                    "asJoinId"
                    (ppr id <+> pprIdDetails (idDetails id)) $
                    id `setIdDetails` JoinId arity
  where
    is_vanilla_or_join id = case idDetails id of
      VanillaId -> True
      JoinId {} -> True
      _ -> False
