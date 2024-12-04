module CSlash.Tc.Gen.CsType where

import CSlash.Cs
import CSlash.Rename.Utils
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.LclEnv
-- import GHC.Tc.Types.Constraint
import CSlash.Tc.Utils.Env
import CSlash.Tc.Utils.TcMType
-- import GHC.Tc.Validity
-- import GHC.Tc.Utils.Unify
-- import GHC.IfaceToCore
import CSlash.Tc.Solver
-- import GHC.Tc.Zonk.Type
import CSlash.Tc.Utils.TcType
-- import GHC.Tc.Utils.Instantiate ( tcInstInvisibleTyBinders, tcInstInvisibleTyBindersN,
--                                   tcInstInvisibleTyBinder, tcSkolemiseInvisibleBndrs,
--                                   tcInstTypeBndrs )
import CSlash.Tc.Zonk.TcType

import CSlash.Core.Type
import CSlash.Core.Type.Rep
import CSlash.Core.Type.Ppr
import CSlash.Core.Kind

import CSlash.Builtin.Types.Prim
import CSlash.Types.Error
import CSlash.Types.Name.Env
import CSlash.Types.Name.Reader( lookupLocalRdrOcc )
import CSlash.Types.Var
import CSlash.Types.Var.Set
import CSlash.Core.TyCon
import CSlash.Core.ConLike
import CSlash.Core.DataCon
-- import CSlash.Core.Class
import CSlash.Types.Name
import CSlash.Types.Var.Env
import CSlash.Builtin.Types
import CSlash.Types.Basic
import CSlash.Types.SrcLoc
import CSlash.Types.Unique
import CSlash.Types.Unique.FM
import CSlash.Utils.Misc
import CSlash.Types.Unique.Supply
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Builtin.Names hiding ( wildCardName )
import CSlash.Driver.DynFlags

import CSlash.Data.FastString
import CSlash.Data.List.Infinite ( Infinite (..) )
import qualified CSlash.Data.List.Infinite as Inf
import CSlash.Data.List.SetOps
import CSlash.Data.Maybe
import CSlash.Data.Bag( unitBag )

import Data.Function ( on )
import Data.List.NonEmpty ( NonEmpty(..), nonEmpty )
import qualified Data.List.NonEmpty as NE
import Data.List ( mapAccumL )
import Control.Monad
import Data.Tuple( swap )

{- *********************************************************************
*                                                                      *
             Kind inference for type declarations
*                                                                      *
********************************************************************* -}

data InitialKindStrategy
  = InitialKindInfer

kcDeclHeader
  :: InitialKindStrategy
  -> Name
  -> TyConFlavor TyCon
  -> [Name]
  -> TcM (Kind, Kind, Arity)
  -> TcM TcTyCon
kcDeclHeader InitialKindInfer = kcInferDeclHeader

-- Note: arity is not the number of args the TyCon can accept,
-- it is the number of args the TyCon accepts before its kind is the result kind
kcInferDeclHeader
  :: Name
  -> TyConFlavor TyCon
  -> [Name]
  -> TcM (Kind, Kind, Arity) -- (resultkind, fullkind, arity)
  -> TcM MonoTcTyCon
kcInferDeclHeader name flav kv_ns kc_res_ki = addTyConFlavCtxt name flav $ do
  (scoped_kvs, (res_kind, full_kind, arity)) <- bindImplicitKinds kv_ns kc_res_ki

  let kv_pairs = mkKiVarNamePairs scoped_kvs
      tycon = mkTcTyCon name res_kind full_kind arity kv_pairs False flav
  
  traceTc "kcInferDeclHeader"
    $ vcat [ ppr name, ppr kv_ns, ppr scoped_kvs, ppr res_kind, ppr full_kind, ppr arity ]

  return tycon

{- *********************************************************************
*                                                                      *
             Expected kinds
*                                                                      *
********************************************************************* -}

data ContextKind
  = TheKind TcKind
  | AnyKind

newExpectedKind :: ContextKind -> TcM TcKind
newExpectedKind (TheKind k) = return k
newExpectedKind AnyKind = newMetaKindVar

{- *********************************************************************
*                                                                      *
             Bringing type variables into scope
*                                                                      *
********************************************************************* -}

newKiVarBndr :: Name -> TcM TcKiVar
newKiVarBndr name = do
  details <- newMetaDetailsK KiVarKind
  return $ mkTcKiVar name details
  
--------------------------------------
--    Implicit kind var binders
--------------------------------------

bindImplicitKinds :: [Name] -> TcM a -> TcM ([TcKiVar], a)
bindImplicitKinds kv_names thing_inside = do
  lcl_env <- getLclTypeEnv
  kvs <- mapM (new_kv lcl_env) kv_names
  traceTc "bindImplicitKinds" (ppr kv_names $$ ppr kvs)
  res <- tcExtendNameKiVarEnv (kv_names `zip` kvs) thing_inside
  return (kvs, res)
  where
    new_kv lcl_env name
      | Just (AKiVar _ kv) <- lookupNameEnv lcl_env name
      = return kv
      | otherwise
      = newKiVarBndr name

{- *********************************************************************
*                                                                      *
             Kind generalization
*                                                                      *
********************************************************************* -}

kindGeneralizeNone :: TcKind -> TcM ()
kindGeneralizeNone kind = do
  traceTc "kindGeneralizeNone" (ppr kind)
  dvs <- candidateQKiVarsOfKind kind
  _ <- promoteKiVarSet $ dVarSetToVarSet dvs
  return ()

{- *********************************************************************
*                                                                      *
             Error messages
*                                                                      *
********************************************************************* -}

addTyConFlavCtxt :: Name -> TyConFlavor tc -> TcM a -> TcM a
addTyConFlavCtxt name flav
  = addErrCtxt $ hsep [ text "In the", ppr flav
                      , text "declaration for"
                      , quotes (ppr name) ]
