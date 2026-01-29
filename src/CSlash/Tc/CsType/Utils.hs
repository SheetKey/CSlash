{-# LANGUAGE DeriveFunctor #-}

module CSlash.Tc.CsType.Utils where

import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Utils.Env
-- import GHC.Tc.Gen.Bind( tcValBinds )
import CSlash.Tc.Utils.TcType

-- import GHC.Builtin.Types( unitTy )
-- import GHC.Builtin.Uniques ( mkBuiltinUnique )

import CSlash.Cs

import CSlash.Core.Type.Rep( Type(..) )
import CSlash.Core.Kind
import CSlash.Core.Type
import CSlash.Core.TyCon
import CSlash.Core.ConLike
import CSlash.Core.DataCon
import CSlash.Core.TyCon.Set

import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc
import CSlash.Utils.FV as FV

import CSlash.Data.Maybe
import CSlash.Data.Bag
import CSlash.Data.FastString

import CSlash.Unit.Module

-- import GHC.Rename.Utils (genHsVar, genLHsApp, genLHsLit, genWildPat)

import CSlash.Types.Basic
-- import GHC.Types.FieldLabel
import CSlash.Types.SrcLoc
import CSlash.Types.SourceFile
import CSlash.Types.SourceText
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Name.Reader ( mkRdrUnqual )
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Unique.Set
import CSlash.Types.TyThing

import Control.Monad

{- *********************************************************************
*                                                                      *
        Cycles in type synonym declarations
*                                                                      *
********************************************************************* -}

type SynCycleState = TyConSet

newtype SynCycleM a = SynCycleM
  { runSynCycleM :: SynCycleState -> Either (SrcSpan, TySynCycleTyCons) (a, SynCycleState) }
  deriving (Functor)

instance Applicative SynCycleM where
  pure x = SynCycleM $ \state -> Right (x, state)
  (<*>) = ap

instance Monad SynCycleM where
  m >>= f = SynCycleM $ \state -> case runSynCycleM m state of
                                    Right (x, state') -> runSynCycleM (f x) state
                                    Left err -> Left err

failSynCycleM :: SrcSpan -> TySynCycleTyCons -> SynCycleM ()
failSynCycleM loc seen_tcs = SynCycleM $ \_ -> Left (loc, seen_tcs)

checkTyConIsAcyclic :: TyCon Zk -> SynCycleM () -> SynCycleM ()
checkTyConIsAcyclic tc m = SynCycleM $ \s ->
  if tc `elemTyConSet` s
  then Right ((), s)
  else case runSynCycleM m s of
         Right ((), s') -> Right ((), extendTyConSet s' tc)
         Left err -> Left err

checkSynCycles :: Unit -> [TyCon Zk] -> [LCsBind Rn] -> TcM ()
checkSynCycles this_uid tcs tyds 
  = case runSynCycleM (mapM_ (go emptyTyConSet []) tcs) emptyTyConSet of
      Left (loc, err) -> setSrcSpan loc $ failWithTc (TcRnTypeSynonymCycle err)
      Right _ -> return ()
    where
      go :: TyConSet -> [TyCon Zk] -> TyCon Zk -> SynCycleM ()
      go so_far seen_tcs tc = checkTyConIsAcyclic tc $ go' so_far seen_tcs tc

      lcl_decls = mkNameEnv (zip (map tyConName tcs) tyds)

      go' :: TyConSet -> [TyCon Zk] -> TyCon Zk -> SynCycleM ()
      go' so_far seen_tcs tc
        | tc `elemTyConSet` so_far
        = failSynCycleM (getSrcSpan (head seen_tcs)) (lookup_decl <$> seen_tcs)
        | not (isHoleModule mod
               || moduleUnit mod == this_uid)
        = return ()
        | Just ty <- synTyConRhs_maybe tc
        = go_ty (extendTyConSet so_far tc) (tc : seen_tcs) ty
        | otherwise = return ()
        where
          mod = nameModule (tyConName tc)
          lookup_decl tc = case lookupNameEnv lcl_decls (tyConName tc) of
                             Just decl -> Right decl
                             Nothing -> Left tc

      go_ty :: TyConSet -> [TyCon Zk] -> Type Zk -> SynCycleM ()
      go_ty so_far seen_tcs ty = mapM_ (go so_far seen_tcs) (synonymTyConsOfType ty)

synonymTyConsOfType :: Type p -> [TyCon p]
synonymTyConsOfType ty = nonDetNameEnvElts (go ty)
  where
    --go :: Type -> NameEnv TyCon
    go (TyConApp tc tys) = go_tc tc `plusNameEnv` go_s tys
    go (TyVarTy _) = emptyNameEnv
    go (AppTy a b) = go a `plusNameEnv` go b
    go (FunTy _ a b) = go a `plusNameEnv` go b
    go (ForAllTy _ ty) = go ty
    go (TyLamTy _ ty) = go ty
    go (BigTyLamTy _ ty) = go ty
    go (CastTy ty _) = go ty
    go (Embed _) = emptyNameEnv
    go (KindCoercion _) = emptyNameEnv
    go other = pprPanic "synonymTyConsOfType" (ppr other)

    go_tc tc | isTypeSynonymTyCon tc = unitNameEnv (tyConName tc) tc
             | otherwise = emptyNameEnv

    go_s tys = foldr (plusNameEnv . go) emptyNameEnv tys

{- *********************************************************************
*                                                                      *
                Building implicits
*                                                                      *
********************************************************************* -}

addTyConsToGblEnv :: [TyCon Zk] -> TcM (TcGblEnv Tc)
addTyConsToGblEnv tys = assertPpr (all isTypeSynonymTyCon tys) (ppr tys) -- temporary
                        $ tcExtendTyConEnv tys
                        --  $ tcExtendGlobalEnvImplicit implicit_things
                        $ do traceTc "tcAddTyCons"
                               $ vcat [ text "tycons" <+> ppr tys ]
                                      -- , text "implicits" <+> ppr implicit_things ]
                             getGblEnv
