module CSlash.Rename.CsKind where

-- import GHC.Core.Type.FVs ( tyCoVarsOfTypeList )
-- import CSlash.Core.TyCon    ( isKindName )
import CSlash.Cs
import CSlash.Rename.Env
-- import GHC.Rename.Doc
import CSlash.Rename.Utils
  ( mapFvRn, bindLocalNamesFV
  , newLocalBndrRn, checkDupRdrNames
  , checkShadowedRdrNames )
import CSlash.Rename.Fixity
--   ( lookupFieldFixityRn, lookupFixityRn, lookupTyFixityRn )
import CSlash.Rename.Unbound ( {-notInScopeErr,-} WhereLooking(WL_LocalOnly) )
import CSlash.Tc.Errors.Types
-- import CSlash.Tc.Errors.Ppr ( pprHsDocContext )
import CSlash.Tc.Utils.Monad
import CSlash.Unit.Module ( getModule )
import CSlash.Types.Name.Reader
import CSlash.Builtin.Names
-- import CSlash.Types.Hint ( UntickedPromotedThing(..) )
import CSlash.Types.Name
import CSlash.Types.SrcLoc
import CSlash.Types.Name.Set
import CSlash.Types.Error

import CSlash.Utils.Misc
import CSlash.Types.Fixity ( compareFixity, negateFixity
                           , Fixity(..), FixityDirection(..), LexicalFixity(..) )
import CSlash.Types.Basic  ( TypeOrKind(..) )
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Data.Maybe

import Data.List (nubBy, partition)
import Control.Monad

{- ******************************************************
*                                                       *
           CsPatSigKind
*                                                       *
****************************************************** -}

data BindKVs = DoBindKVs | AlreadyBoundKVs

rnCsPatSigKind
  :: BindKVs
  -> CsDocContext
  -> CsPatSigKind Ps
  -> (CsPatSigKind Rn -> RnM (a, FreeVars))
  -> RnM (a, FreeVars)
rnCsPatSigKind bindkvs ctx sig_ki thing_inside = do
  let pat_sig_ki = csPatSigKind sig_ki
      env = RKE ctx
  do_first $ \imp_kvs -> do
    (pat_sig_ki', fvs1) <- rnLCsKi env pat_sig_ki
    let sig_ki' = CsPSK (CsPSKRn imp_kvs) pat_sig_ki'
    (res, fvs2) <- thing_inside sig_ki'
    return (res, fvs1 `plusFV` fvs2)                              
  where
    do_first f = case bindkvs of
      DoBindKVs -> do
        let kv_occs = extractCsPatSigKindKindVars sig_ki
        rnImplicitKvOccs kv_occs f
      AlreadyBoundKVs -> f []

{- ******************************************************
*                                                       *
           LCsKind and CsKind
*                                                       *
****************************************************** -}

data RnKiEnv = RKE
  { rke_ctxt :: CsDocContext
  }

mkKiEnv :: CsDocContext -> RnKiEnv
mkKiEnv ctxt = RKE ctxt

rnLCsKind :: CsDocContext -> LCsKind Ps -> RnM (LCsKind Rn, FreeVars)
rnLCsKind ctxt kind = rnLCsKi (mkKiEnv ctxt) kind

rnLCsKi :: RnKiEnv -> LCsKind Ps -> RnM (LCsKind Rn, FreeVars)
rnLCsKi env (L loc ki) = setSrcSpanA loc $ do
  (ki', fvs) <- rnCsKi env ki
  return (L loc ki', fvs)

rnCsKi :: RnKiEnv -> CsKind Ps -> RnM (CsKind Rn, FreeVars)
rnCsKi _ (CsUKd {}) = return (CsUKd noExtField, emptyFVs)
rnCsKi _ (CsAKd {}) = return (CsAKd noExtField, emptyFVs)
rnCsKi _ (CsLKd {}) = return (CsLKd noExtField, emptyFVs)
rnCsKi env (CsKiVar _ ln@(L loc rdr_name)) = do
  massertPpr (isRdrKiVar rdr_name) (text "rnCsKi CsKiVar" <+> ppr ln)
  name <- rnKiVar env rdr_name
  return (CsKiVar noAnn (L loc name), unitFV name)  
rnCsKi env (CsFunKi _ ki1 ki2) = do
  (ki1', fvs1) <- rnLCsKi env ki1
  (ki2', fvs2) <- rnLCsKi env ki2
  return (CsFunKi noExtField ki1' ki2', fvs1 `plusFV` fvs2)
rnCsKi env (CsParKd _ ki) = do
  (ki', fvs) <- rnLCsKi env ki
  return (CsParKd noAnn ki', fvs)

rnKiContext :: CsDocContext -> LCsContext Ps -> RnM (LCsContext Rn, FreeVars)
rnKiContext ctxt = wrapLocFstMA $ mapFvRn $ rnCsKdRel ctxt
 
rnCsKdRel :: CsDocContext -> LCsKdRel Ps -> RnM (LCsKdRel Rn, FreeVars)
rnCsKdRel ctxt (L l (CsKdLT _ ki1 ki2)) = do
  (ki1', fvs1) <- rnLCsKind ctxt ki1
  (ki2', fvs2) <- rnLCsKind ctxt ki2
  return (L l (CsKdLT noAnn ki1' ki2'), fvs1 `plusFV` fvs2)
rnCsKdRel ctxt (L l (CsKdLTEQ _ ki1 ki2)) = do
  (ki1', fvs1) <- rnLCsKind ctxt ki1
  (ki2', fvs2) <- rnLCsKind ctxt ki2
  return (L l (CsKdLTEQ noAnn ki1' ki2'), fvs1 `plusFV` fvs2)
  

rnKiVar :: RnKiEnv -> RdrName -> RnM Name
rnKiVar env rdr_name = do
  name <- lookupKindOccRn rdr_name
  checkWildCardKi env name
  return name

checkWildCardKi :: RnKiEnv -> Name -> RnM ()
checkWildCardKi env name =
  if startsWithUnderscore (nameOccName name)
  then panic "addErr $ TcRnWithCsDocContext (rke_ctxt env) $"
                --TcRnIllegalWildCardInKind name
  else return ()

-- Create new renamed kind variables corresponding to source-level ones.
-- Duplicates are permitted, and will be removed here. This handles 
-- free kind variables in a type signature, all of which are implicitly bound.
rnImplicitKvOccs :: FreeKiVars -> ([Name] -> RnM (a, FreeVars)) -> RnM (a, FreeVars)
rnImplicitKvOccs implicit_vs_with_dups thing_inside = do
  massertPpr (all (isRdrKiVar . unLoc) implicit_vs_with_dups)
    (text "rnImplicitKvOccs: Contains non kind var name:"
     <+> ppr implicit_vs_with_dups)
  let implicit_vs = nubN implicit_vs_with_dups
  loc <- getSrcSpanM
  let loc' = noAnnSrcSpan loc
  vars <- mapM (newKiVarNameRnImplicit . L loc' . unLoc) implicit_vs
  traceRn "rnImplicitKvOccs" $
    vcat [ ppr implicit_vs_with_dups, ppr implicit_vs, ppr vars ]
  bindLocalNamesFV vars $ thing_inside vars

newKiVarNameRnImplicit :: LocatedN RdrName -> RnM Name
newKiVarNameRnImplicit = new_ki_name_rn $ \lrdr ->
  newLocalBndrRn lrdr

new_ki_name_rn :: (LocatedN RdrName -> RnM Name) -> LocatedN RdrName -> RnM Name
new_ki_name_rn cont lrdr = cont lrdr

{- *********************************************************************
*                                                                      *
      Finding the free kind variables of a (CsType RdrName)
*                                                                      *
********************************************************************* -}


type FreeKiVars = [LocatedN RdrName]

filterInScope :: (GlobalRdrEnv, LocalRdrEnv) -> FreeKiVars -> FreeKiVars
filterInScope envs = filterOut (inScope envs . unLoc)

filterInScopeM :: FreeKiVars -> RnM FreeKiVars
filterInScopeM vars = do
  envs <- getRdrEnvs
  return (filterInScope envs vars)

inScope :: (GlobalRdrEnv, LocalRdrEnv) -> RdrName -> Bool
inScope (gbl, lcl) rdr = rdr_in_scope
  where
    rdr_in_scope = elem_lcl rdr

    elem_lcl name = elemLocalRdrEnv name lcl

nubN :: Eq a => [LocatedN a] -> [LocatedN a]
nubN = nubBy eqLocated
  
extractCsPatSigKindKindVars :: CsPatSigKind (NoTc Ps) -> FreeKiVars
extractCsPatSigKindKindVars (CsPSK _ ki) = extractCsKindKindVars ki

extractCsKindKindVars :: LCsKind Ps -> FreeKiVars
extractCsKindKindVars ki = extract_lki ki []

extract_lki :: LCsKind Ps -> FreeKiVars -> FreeKiVars
extract_lki (L _ ki) acc = case ki of
  CsUKd {} -> acc
  CsAKd {} -> acc
  CsLKd {} -> acc
  CsKiVar _ lkv -> extract_kv lkv acc
  CsFunKi _ ki1 ki2 -> extract_lki ki1 $ extract_lki ki2 acc
  CsParKd _ ki -> extract_lki ki acc

extract_kv :: LocatedN RdrName -> FreeKiVars -> FreeKiVars
extract_kv kv acc =
  assertPpr (isRdrKiVar (unLoc kv) && (not . isQual) (unLoc kv)) (text "extact_kv:" <+> ppr kv)
  $ kv : acc
