module CSlash.Tc.Validity where

import CSlash.Data.FastString

import CSlash.Data.Maybe

-- friends:
-- import GHC.Tc.Utils.Unify    ( tcSubTypeAmbiguity )
-- import GHC.Tc.Solver         ( simplifyAmbiguityCheck )
-- import GHC.Tc.Instance.Class ( matchGlobalInst, ClsInstResult(..), AssocInstInfo(..) )
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Types.Origin
-- import GHC.Tc.Types.Rank
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad
-- import GHC.Tc.Instance.FunDeps
-- import GHC.Tc.Instance.Family
import CSlash.Tc.Zonk.TcType

import CSlash.Builtin.Types
import CSlash.Builtin.Names
import CSlash.Builtin.Uniques  ( mkAlphaTyVarUnique )

import CSlash.Core.Type
import CSlash.Core.Type.Tidy
import CSlash.Core.Kind
-- import GHC.Core.Unify ( typesAreApart, tcMatchTyX_BM, BindFlag(..) )
-- import GHC.Core.Coercion
-- import GHC.Core.Coercion.Axiom
-- import GHC.Core.Class
import CSlash.Core.TyCon
-- import GHC.Core.Predicate
import CSlash.Core.Type.FVs
import CSlash.Core.Type.Rep
import CSlash.Core.Type.Ppr
-- import GHC.Core.FamInstEnv ( isDominatedBy, injectiveBranches
--                            , InjectivityCheckResult(..) )

import CSlash.Cs
import CSlash.Driver.Session

import CSlash.Types.Error
import CSlash.Types.Basic   ( TypeOrKind(..) )
import CSlash.Types.Name
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Var
import CSlash.Types.SourceFile
import CSlash.Types.SrcLoc
import CSlash.Types.TyThing ( TyThing(..) )
import CSlash.Types.Unique.Set( isEmptyUniqSet )

-- import CSlash.Utils.FV
import CSlash.Utils.Error
import CSlash.Utils.Misc
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic

import CSlash.Data.List.SetOps

import Control.Monad
import Data.Foldable
import Data.Function
import Data.List        ( (\\) )
import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty ( NonEmpty(..) )
import Data.Bifunctor (bimap)

{- *********************************************************************
*                                                                      *
          Checking validity of a kind
*                                                                      *
********************************************************************* -}

checkValidKind :: UserTypeCtxt -> Kind Tc -> TcM ()
checkValidKind _ctxt ki = traceTc "checkValidKind" (ppr ki)

checkValidMonoKind :: UserTypeCtxt -> MonoKind Tc -> TcM ()
checkValidMonoKind _ctxt ki = traceTc "checkValidKind" (ppr ki)

{- *********************************************************************
*                                                                      *
          Checking for ambiguity
*                                                                      *
*********************************************************************_-}

checkAmbiguity :: UserTypeCtxt -> Type p -> TcM ()
checkAmbiguity ctxt ty = traceTc "Ambiguity check NOT IMPLEMENTED" empty

checkUserTypeError :: UserTypeCtxt -> Type p -> TcM ()
checkUserTypeError ctxt ty
  | TySynCtxt  {} <- ctxt
  = return ()
  | otherwise --Just msg <- deepUserTypeError_maybe ty
  = traceTc "checkUserTypeError: UNFINISHED**************************" empty

{- *********************************************************************
*                                                                      *
          Checking validity of a user-defined type
*                                                                      *
********************************************************************* -}

checkValidTcType :: UserTypeCtxt -> Type Tc -> TcM ()
checkValidTcType ctxt ty = do
  traceTc "checkValidTcType" (ppr ty <+> colon <+> ppr (typeKind ty))
  env <- liftZonkM $ tcInitOpenTidyEnv $ varsOfTypeList ty
  let ve = ValidityEnv { ve_tidy_env = env
                       , ve_ctxt = ctxt }

  checkNoErrs $ do
    check_type ve ty
    checkUserTypeError ctxt ty
    traceTc "done ct" (ppr ty)

  checkAmbiguity ctxt ty

  traceTc "checkValidTcType done" (ppr ty <+> colon <+> ppr (typeKind ty))

-- TODO: Check that kvs and kcvs only appear at the top level!
checkValidType :: UserTypeCtxt -> Type Zk -> TcM ()
checkValidType ctxt ty = do
  traceTc "checkValidType" (ppr ty <+> colon <+> ppr (typeKind ty))
  let env = tidyFreeVars emptyTidyEnv (varsOfTypeList ty)
  let ve = ValidityEnv { ve_tidy_env = env
                       , ve_ctxt = ctxt }
  checkNoErrs $ do
    check_type ve ty
    checkUserTypeError ctxt ty
    traceTc "done ct" (ppr ty)

  checkAmbiguity ctxt ty

  traceTc "checkValidType done" (ppr ty <+> colon <+> ppr (typeKind ty))

-- used for checking if the rhs returns a constraint
checkTySynRhs :: UserTypeCtxt -> Type Zk -> TcM ()
checkTySynRhs ctxt ty = return ()
  
data ValidityEnv p = ValidityEnv
  { ve_tidy_env :: TidyEnv p
  , ve_ctxt :: UserTypeCtxt }

instance Outputable (ValidityEnv p) where
  ppr (ValidityEnv { ve_tidy_env = env
                   , ve_ctxt = ctxt })
    = hang (text "ValidityEnv")
           2 (vcat [ text "ve_tidy_env" <+> ppr env
                   , text "ve_ctxt" <+> pprUserTypeCtxt ctxt ])

check_type :: ValidityEnv p -> Type p -> TcM ()

check_type _ (TyVarTy _) = return ()

check_type _ (Embed _) = return ()

check_type ve (AppTy ty1 ty2) = do
  check_type ve ty1
  check_arg_type ve ty2

check_type ve ty@(TyConApp tc tys)
  | isTypeSynonymTyCon tc
  = check_syn_tc_app ve ty tc tys
  | otherwise
  = mapM_ (check_arg_type ve) tys

check_type ve (CastTy ty _) = check_type ve ty

check_type ve@(ValidityEnv { ve_tidy_env = env }) ty
  | not (null tvbs)
  = do traceTc "check_type/FA" (ppr ty)
       check_type (ve { ve_tidy_env = env' }) tau
  where
    (tvbs, tau) = tcSplitForAllTyVarBinders ty
    (env', _) = panic "tidyForAllTyBinders env tvbs"

check_type ve@(ValidityEnv { ve_tidy_env = env }) ty
  | not (null tvbs)
  = do traceTc "check_type/TL" (ppr ty)
       check_type (ve { ve_tidy_env = env' }) rhs
  where
    (tvbs, rhs) = tcSplitTyLamTyVarBinders ty
    (env', _) = panic "tidyTyLamTyBinders env tvbs"

check_type ve@(ValidityEnv { ve_tidy_env = env }) ty
  | not (null kvbs)
  = do traceTc "check_type/BTL" (ppr ty)
       check_type (ve { ve_tidy_env = env' }) rhs
  where
    (kvbs, rhs) = tcSplitBigLamTyVarBinders ty
    (env', _) = panic "tidyBigLamTyBinders env kvbs"

check_type ve ty@(FunTy _ arg_ty res_ty) = do
  check_type ve arg_ty
  check_type ve res_ty

check_type _ ty@(ForAllTy {}) = pprPanic "check_type/FA2" (ppr ty)
check_type _ ty@(TyLamTy {}) = pprPanic "check_type/TL2" (ppr ty)
check_type _ ty@(BigTyLamTy {}) = pprPanic "check_type/BTL2" (ppr ty)
check_type _ other = pprPanic "check_type/O" (ppr other)

check_syn_tc_app
  :: ValidityEnv p
  -> Type p
  -> TyCon p
  -> [Type p]
  -> TcM ()
check_syn_tc_app (ve@ValidityEnv { ve_ctxt = ctxt }) ty tc tys
  | tys `lengthAtLeast` tc_arity
  = check_expansion_only 
  | otherwise
  = failWithTc (tyConArityErr tc tys)
  where
    tc_arity = tyConArity tc

    check_expansion_only :: TcM ()
    check_expansion_only = assertPpr (isTypeSynonymTyCon tc) (ppr tc) $
      case coreView ty of
        Just ty' -> let err_ctxt = text "In the expansion of type synonym"
                                   <+> quotes (ppr tc)
                    in addErrCtxt err_ctxt $ check_type ve ty'
        Nothing -> pprPanic "check_syn_tc_app" (ppr ty)

-- NOT for type synonyms. We always expand type synonyms (Like LiberalTypeSynonyms extension)
-- so we do not EVER check the args of a type synonym
check_arg_type :: ValidityEnv p -> Type p -> TcM ()
check_arg_type _ (KindCoercion {}) = return ()
check_arg_type ve@(ValidityEnv { ve_ctxt = ctxt }) ty = check_type ve ty

tyConArityErr :: TyCon p -> [Type p] -> TcRnMessage
tyConArityErr tc tks = panic "TcRnArityMismatch (ATyCon tc) tc_type_arity tc_type_args"
  where
    tc_type_arity = tyConArity tc
    tc_type_args = length tks
