{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module CSlash.Stg.Lift.Monad where

import CSlash.Core as C

import CSlash.Types.Basic
-- import GHC.Types.CostCentre ( isCurrentCCS, dontCareCCS )
import CSlash.Data.FastString
import CSlash.Types.Var
import CSlash.Types.Var.Id
import CSlash.Types.Name
import CSlash.Utils.Outputable
import CSlash.Data.OrdList

import CSlash.Stg.Lift.Config
import CSlash.Stg.Subst
import CSlash.Stg.Syntax

import CSlash.Core.Utils
import CSlash.Types.Unique.Supply
import CSlash.Utils.Panic
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Core.Kind

import Control.Arrow ( second )
import Control.Monad.Trans.Class
import Control.Monad.Trans.RWS.Strict ( RWST, runRWST )
import qualified Control.Monad.Trans.RWS.Strict as RWS
import Control.Monad.Trans.Cont ( ContT (..), runContT )
import Data.ByteString ( ByteString )

decomposeStgBinding :: GenStgBinding pass -> (RecFlag, [(BinderP pass, GenStgRhs pass)])
decomposeStgBinding (StgRec pairs) = (Recursive, pairs)
decomposeStgBinding (StgNonRec bndr rhs) = (NonRecursive, [(bndr, rhs)])

mkStgBinding :: RecFlag -> [(BinderP pass, GenStgRhs pass)] -> GenStgBinding pass
mkStgBinding Recursive = StgRec
mkStgBinding NonRecursive = uncurry StgNonRec . head

data Env = Env
  { e_config :: StgLiftConfig
  , e_subst :: !StgSubst
  , e_expansions :: !(VarEnv CoreId DCoreIdSet)
  }

emptyEnv :: StgLiftConfig -> Env
emptyEnv cfg = Env
  { e_config = cfg
  , e_subst = emptySubst
  , e_expansions = emptyVarEnv
  }

data FloatLang
  = StartBindingGroup
  | EndBindingGroup
  | PlainTopBinding OutStgTopBinding
  | LiftedBinding OutStgBinding

instance Outputable FloatLang where
  ppr StartBindingGroup = char '('
  ppr EndBindingGroup = char ')'
  ppr (PlainTopBinding StgTopStringLit{}) = text "<str>"
  ppr (PlainTopBinding (StgTopBind b)) = ppr (LiftedBinding b)
  ppr (LiftedBinding bind) = (if isRec is_rec then char 'r' else char 'n') <+> ppr (map fst pairs)
    where
      (is_rec, pairs) = decomposeStgBinding bind

collectFloats :: [FloatLang] -> [OutStgTopBinding]
collectFloats = go (0 :: Int) []
  where
    go 0 [] [] = []
    go _ _ [] = pprPanic "collectFloats" (text "unterminated group")
    go n binds (f:rest) = case f of
      StartBindingGroup -> go (n + 1) binds rest
      EndBindingGroup
        | n == 0 -> pprPanic "collectFloats" (text "no group to end")
        | n == 1 -> StgTopBind (merge_binds binds) : go 0 [] rest
        | otherwise -> go (n - 1) binds rest
      PlainTopBinding top_bind
        | n == 0 -> top_bind : go n binds rest
        | otherwise -> pprPanic "collectFloats" (text "plain top binding inside group")
      LiftedBinding bind
        | n == 0 -> StgTopBind (rm_cccs bind) : go n binds rest
        | otherwise -> go n (bind:binds) rest

    map_rhss f = uncurry mkStgBinding . second (map (second f)) . decomposeStgBinding
    rm_cccs = map_rhss removeRhsCCCs

    merge_binds binds = assert (any is_rec binds) $
                        StgRec (concatMap (snd . decomposeStgBinding . rm_cccs) binds)

    is_rec StgRec{} = True
    is_rec _ = False

removeRhsCCCs :: GenStgRhs pass -> GenStgRhs pass
removeRhsCCCs (StgRhsClosure ext bndrs body ty) = StgRhsClosure ext bndrs body ty
removeRhsCCCs (StgRhsCon con mu ts args ty) = StgRhsCon con mu ts args ty
removeRhsCCCs rhs = rhs

newtype LiftM a = LiftM
  { unwrapLiftM :: RWST Env (OrdList FloatLang) () UniqSM a }
  deriving (Functor, Applicative, Monad)

instance MonadUnique LiftM where
  getUniqueSupplyM = LiftM (lift getUniqueSupplyM)
  getUniqueM = LiftM (lift getUniqueM)
  getUniquesM = LiftM (lift getUniquesM)

runLiftM :: StgLiftConfig -> UniqSupply -> LiftM () -> [OutStgTopBinding]
runLiftM cfg us (LiftM m) = collectFloats (fromOL floats)
  where
    (_, _, floats) = initUs_ us (runRWST m (emptyEnv cfg) ())

getConfig :: LiftM StgLiftConfig
getConfig = LiftM $ e_config <$> RWS.ask

startBindingGroup :: LiftM ()
startBindingGroup = LiftM $ RWS.tell $ unitOL $ StartBindingGroup

endBindingGroup :: LiftM ()
endBindingGroup = LiftM $ RWS.tell $ unitOL $ EndBindingGroup

addLiftedBinding :: OutStgBinding -> LiftM ()
addLiftedBinding = LiftM . RWS.tell . unitOL . LiftedBinding

withSubstBndr :: CoreId -> (CoreId -> LiftM a) -> LiftM a
withSubstBndr bndr inner = LiftM $ do
  subst <- RWS.asks e_subst
  let (bndr', subst') = substBndr bndr subst
  RWS.local (\e -> e { e_subst = subst' }) (unwrapLiftM (inner bndr'))

withSubstBndrs :: Traversable f => f CoreId -> (f CoreId -> LiftM a) -> LiftM a
withSubstBndrs = runContT . traverse (ContT . withSubstBndr)

withLiftedBndr :: DCoreIdSet -> CoreId -> (CoreId -> LiftM a) -> LiftM a
withLiftedBndr abs_ids bndr inner = do
  let str = fsLit "$l" `appendFS` occNameFS (getOccName bndr)
      abs_bndrs = (, Just (BIKi UKd)) . C.Id <$> dVarSetElems abs_ids
      ty = mkLamTypes abs_bndrs (varType bndr)
  bndr' <- transferPolyIdInfo bndr abs_bndrs
           <$> mkSysLocalM str ty
  LiftM $ RWS.local
    (\e -> e { e_subst = extendSubst bndr bndr' $ extendInScope bndr' $ e_subst e
             , e_expansions = extendVarEnv (e_expansions e) bndr abs_ids }
    )
    (unwrapLiftM (inner bndr'))

withLiftedBndrs :: Traversable f => DCoreIdSet -> f CoreId -> (f CoreId -> LiftM a) -> LiftM a
withLiftedBndrs abs_ids = runContT . traverse (ContT . withLiftedBndr abs_ids)

substOcc :: CoreId -> LiftM CoreId
substOcc id = LiftM (RWS.asks (lookupIdSubst id . e_subst))

isLifted :: InId -> LiftM Bool
isLifted bndr = LiftM (RWS.asks (elemVarEnv bndr . e_expansions))

formerFreeVars :: InId -> LiftM [OutId]
formerFreeVars f = LiftM $ do
  expansions <- RWS.asks e_expansions
  pure $ case lookupVarEnv expansions f of
    Nothing -> []
    Just fvs -> dVarSetElems fvs

liftedIdsExpander :: LiftM (DCoreIdSet -> DCoreIdSet)
liftedIdsExpander = LiftM $ do
  expansions <- RWS.asks e_expansions
  subst <- RWS.asks e_subst
  let go set fv = case lookupVarEnv expansions fv of
        Nothing -> extendDVarSet set (noWarnLookupIdSubst fv subst)
        Just fvs' -> unionDVarSet set fvs'
      expander fvs = foldl' go emptyDVarSet (dVarSetElems fvs)
  pure expander
