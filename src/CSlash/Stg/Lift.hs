{-# LANGUAGE BangPatterns #-}

module CSlash.Stg.Lift (StgLiftConfig(..), stgLiftLams) where

import CSlash.Core (CoreId)

import CSlash.Types.Basic
import CSlash.Types.Var.Id
import CSlash.Stg.FVs ( annBindingFreeVars )
import CSlash.Stg.Lift.Config
import CSlash.Stg.Lift.Analysis
import CSlash.Stg.Lift.Monad
import CSlash.Stg.Syntax
import CSlash.Unit.Module (Module)
import CSlash.Types.Unique.Supply
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Types.Var.Set
import Control.Monad ( when )
import Data.Maybe ( isNothing )

stgLiftLams :: Module -> StgLiftConfig -> UniqSupply -> [InStgTopBinding] -> [OutStgTopBinding]
stgLiftLams this_mod cfg us = runLiftM cfg us . foldr (liftTopLvl this_mod) (pure ())

liftTopLvl :: Module -> InStgTopBinding -> LiftM () -> LiftM ()
liftTopLvl _ (StgTopStringLit {}) rest = panic "liftTopLvl StringLit"

liftTopLvl this_mod (StgTopBind bind) rest = do
  let is_rec = isRec $ fst $ decomposeStgBinding bind
  when is_rec startBindingGroup
  let bind_w_fvs = annBindingFreeVars this_mod bind
  withLiftedBind TopLevel (tagSkeletonTopBind bind_w_fvs) NilSk $ \mb_bind' -> do
    case mb_bind' of
      Nothing -> pprPanic "StgLiftLams" (text "Lifted top-level binding")
      Just bind' -> addLiftedBinding bind'
    when is_rec endBindingGroup
    rest

withLiftedBind
  :: TopLevelFlag
  -> LlStgBinding
  -> Skeleton
  -> (Maybe OutStgBinding -> LiftM a)
  -> LiftM a
withLiftedBind top_lvl bind scope k
  = withLiftedBindPairs top_lvl is_rec pairs scope (k . fmap (mkStgBinding is_rec))
  where
    (is_rec, pairs) = decomposeStgBinding bind

withLiftedBindPairs
  :: TopLevelFlag
  -> RecFlag
  -> [(BinderInfo, LlStgRhs)]
  -> Skeleton
  -> (Maybe [(CoreId, OutStgRhs)] -> LiftM a)
  -> LiftM a
withLiftedBindPairs top is_rec pairs scope k = do
  let (infos, rhss) = unzip pairs
      bndrs = map binderInfoBndr infos
  expander <- liftedIdsExpander
  cfg <- getConfig
  case goodToLift cfg top is_rec expander pairs scope of
    Just abs_ids -> withLiftedBndrs abs_ids bndrs $ \bndrs' -> do
      when (isRec is_rec) startBindingGroup
      rhss' <- traverse (liftRhs (Just abs_ids)) rhss
      let pairs' = zip bndrs' rhss'
      addLiftedBinding (mkStgBinding is_rec pairs')
      when (isRec is_rec) endBindingGroup
      k Nothing
    Nothing -> withSubstBndrs bndrs $ \bndrs' -> do
      rhss' <- traverse (liftRhs Nothing) rhss
      let pairs' = zip bndrs' rhss'
      k (Just pairs')

liftRhs
  :: Maybe DCoreIdSet
  -> LlStgRhs
  -> LiftM OutStgRhs
liftRhs mb_former_fvs rhs@(StgRhsCon con mn ts args ty)
  = assertPpr (isNothing mb_former_fvs)
    (text "Should never lift a constructor"
     $$ pprStgRhs panicStgPprOpts rhs) $
    StgRhsCon con mn ts <$> traverse liftArgs args <*> pure ty
    
liftRhs Nothing (StgRhsClosure _ is_join infos body ty)
  = withSubstBndrs (map binderInfoBndr infos) $ \bndrs' ->
    StgRhsClosure noExtFieldSilent is_join bndrs' <$> liftExpr body <*> pure ty  

liftRhs (Just former_fvs) (StgRhsClosure _ is_join infos body ty)
  = withSubstBndrs (map binderInfoBndr infos) $ \bndrs' -> do
    let bndrs'' = dVarSetElems former_fvs ++ bndrs'
    StgRhsClosure noExtFieldSilent is_join bndrs'' <$> liftExpr body <*> pure ty

liftArgs :: InStgArg -> LiftM OutStgArg
liftArgs a@(StgLitArg _) = pure a
liftArgs (StgVarArg occ) = do
  assertPprM (not <$> isLifted occ) (text "StgArgs should never be lifted" $$ ppr occ)
  StgVarArg <$> substOcc occ

liftExpr :: LlStgExpr -> LiftM OutStgExpr
liftExpr (StgLit lit) = pure (StgLit lit)
liftExpr (StgTick t e) = StgTick t <$> liftExpr e
liftExpr (StgApp f args) = do
  f' <- substOcc f
  args' <- traverse liftArgs args
  fvs' <- formerFreeVars f
  let top_lvl_args = map StgVarArg fvs' ++ args'
  pure (StgApp f' top_lvl_args)
liftExpr (StgConApp con mn args tys) = StgConApp con mn <$> traverse liftArgs args <*> pure tys
liftExpr (StgOpApp op args ty) = StgOpApp op <$> traverse liftArgs args <*> pure ty
liftExpr (StgCase scrut info ty alts) = do
  scrut' <- liftExpr scrut
  withSubstBndr (binderInfoBndr info) $ \bndr' -> do
    alts' <- traverse liftAlt alts
    pure (StgCase scrut' bndr' ty alts')
liftExpr (StgLet scope bind body)
  = withLiftedBind NotTopLevel bind scope $ \mb_bind' -> do
      body' <- liftExpr body
      case mb_bind' of
        Nothing -> pure body'
        Just bind' -> pure (StgLet noExtFieldSilent bind' body')
liftExpr (StgLetNoEscape scope bind body)
  = withLiftedBind NotTopLevel bind scope $ \mb_bind' -> do
      body' <- liftExpr body
      case mb_bind' of
        Nothing -> pprPanic "stgLiftLams" (text "Should never decide to lift LNEs")
        Just bind' -> pure (StgLetNoEscape noExtFieldSilent bind' body')

liftAlt :: LlStgAlt -> LiftM OutStgAlt
liftAlt alt@GenStgAlt{ alt_bndrs = infos, alt_rhs = rhs }
  = withSubstBndrs (map binderInfoBndr infos) $ \bndrs' -> do
      !rhs' <- liftExpr rhs
      return $! alt { alt_bndrs = bndrs', alt_rhs = rhs' }
