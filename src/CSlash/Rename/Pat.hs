{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}

module CSlash.Rename.Pat where

-- import {-# SOURCE #-} GHC.Rename.Expr ( rnLExpr )
-- import {-# SOURCE #-} GHC.Rename.Splice ( rnSplicePat, rnSpliceTyPat )

import CSlash.Cs
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad
-- import GHC.Tc.Utils.TcMType ( hsOverLitName )
import CSlash.Rename.Env
import CSlash.Rename.Fixity
import CSlash.Rename.Utils
  ( newLocalBndrRn, bindLocalNames, warnUnusedMatches, newLocalBndrRn
  , checkDupNames, checkDupAndShadowedNames
  , wrapGenSpan{-, genCsApps, genLCsVar, genCsIntegralLit, delLocalNames, typeAppErr-} )
import CSlash.Rename.CsType
import CSlash.Rename.CsKind
import CSlash.Builtin.Names

import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.Name.Reader
import CSlash.Types.Unique.Set

import CSlash.Types.Basic
import CSlash.Types.SourceText
import CSlash.Utils.Misc
import CSlash.Data.FastString ( uniqCompareFS )
import CSlash.Data.List.SetOps( removeDups )
import CSlash.Data.Bag ( Bag, unitBag, unionBags, emptyBag, listToBag, bagToList )
import CSlash.Utils.Outputable
import CSlash.Utils.Panic.Plain
import CSlash.Types.SrcLoc
import CSlash.Types.Literal   ( inCharRange )
import CSlash.Types.GREInfo   ( ConInfo(..){-, conInfoFields-} )
-- import CSlash.Builtin.Types   ( nilDataCon )
import CSlash.Core.DataCon
-- import CSlash.Core.TyCon      ( isKindName )

import Control.Monad       ( when, ap, guard, unless )
import Data.Foldable
import Data.Function       ( on )
import Data.Functor.Identity ( Identity (..) )
import qualified Data.List.NonEmpty as NE
import Data.Maybe
import Data.Ratio
import qualified Data.Semigroup as S
import Control.Monad.Trans.Writer.CPS
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Data.Functor ((<&>))
-- import GHC.Rename.Doc (rnLHsDoc)
import CSlash.Types.Hint
import CSlash.Types.Fixity (LexicalFixity(..))
import Data.Coerce

{- *****************************************************
*                                                      *
        The CpsRn Monad
*                                                      *
***************************************************** -}

newtype CpsRn b = CpsRn { unCpsRn :: forall r. (b -> RnM (r, FreeVars)) -> RnM (r, FreeVars) }
  deriving (Functor)

instance Applicative CpsRn where
  pure x = CpsRn (\k -> k x)
  (<*>) = ap

instance Monad CpsRn where
  (CpsRn m) >>= mk = CpsRn (\k -> m (\v -> unCpsRn (mk v) k))

runCps :: CpsRn a -> RnM (a, FreeVars)
runCps (CpsRn m) = m (\r -> return (r, emptyFVs))

liftCps :: RnM a -> CpsRn a
liftCps rn_thing = CpsRn (\k -> rn_thing >>= k)

liftCpsFV :: RnM (a, FreeVars) -> CpsRn a
liftCpsFV rn_thing = CpsRn (\k -> do (v, fvs1) <- rn_thing
                                     (r, fvs2) <- k v
                                     return (r, fvs1 `plusFV` fvs2))

liftCpsWithCont :: (forall r. (b -> RnM (r, FreeVars)) -> RnM (r, FreeVars)) -> CpsRn b
liftCpsWithCont = CpsRn

wrapSrcSpanCps :: (a -> CpsRn b) -> LocatedA a -> CpsRn (LocatedA b)
wrapSrcSpanCps fn (L loc a) = CpsRn (\k -> setSrcSpanA loc $ unCpsRn (fn a) $ \v -> k (L loc v))

{- *****************************************************
*                                                      *
        Name makers
*                                                      *
***************************************************** -}

data NameMaker
  = LamMk Bool
  | LetMk TopLevelFlag MiniFixityEnv

topRecNameMaker :: MiniFixityEnv -> NameMaker
topRecNameMaker fix_env = LetMk TopLevel fix_env

localRecNameMaker :: MiniFixityEnv -> NameMaker
localRecNameMaker fix_env = LetMk NotTopLevel fix_env

matchNameMaker :: CsMatchContext fn -> NameMaker
matchNameMaker _ = LamMk True

newPatLName :: NameMaker -> LocatedN RdrName -> CpsRn (LocatedN Name)
newPatLName name_maker rdr_name@(L loc _) = (L loc) <$>  newPatName name_maker rdr_name

newPatName :: NameMaker -> LocatedN RdrName -> CpsRn Name
newPatName (LamMk report_unused) rdr_name = CpsRn $ \ thing_inside -> do
  name <- newLocalBndrRn rdr_name
  (res, fvs) <- bindLocalNames [name] (thing_inside name)
  when report_unused $ warnUnusedMatches [name] fvs
  return (res, name `delFV` fvs)
newPatName (LetMk is_top fix_env) rdr_name = CpsRn $ \ thing_inside -> do
  name <- case is_top of
            NotTopLevel -> newLocalBndrRn rdr_name
            TopLevel -> newTopSrcBinder rdr_name
  bindLocalNames [name]
    $ addLocalFixities fix_env [name]
    $ thing_inside name

{- *****************************************************
*                                                      *
        External entry points
*                                                      *
***************************************************** -}

{-# INLINE rn_pats_general #-}
rn_pats_general
  :: Traversable f
  => BindKVs
  -> CsMatchContextRn
  -> f (LPat Ps)
  -> (f (LPat Rn) -> RnM (r, FreeVars))
  -> RnM (r, FreeVars)
rn_pats_general bindkvs ctxt pats thing_inside = do
  envs_before <- getRdrEnvs

  unCpsRn (rn_pats_fun (matchNameMaker ctxt) pats) $ \ pats' -> do
    let bndrs = collectPatsBinders CollVarTyVarBinders (toList pats')
    addErrCtxt doc_pat $ if isPatSynCtxt ctxt
                         then checkDupNames bndrs
                         else checkDupAndShadowedNames envs_before bndrs
    thing_inside pats'
  where
    doc_pat = text "In" <+> pprMatchContext ctxt

    rn_pats_fun = case ctxt of
      LamAlt -> mapM . rnLArgPatAndThen bindkvs
      TyLamAlt -> mapM . rnLArgPatAndThen bindkvs
      TyLamTyAlt -> mapM . rnLArgPatAndThen bindkvs
      _ -> mapM . rnLPatAndThen bindkvs

rnPats
  :: BindKVs
  -> CsMatchContextRn
  -> [LPat Ps]
  -> ([LPat Rn] -> RnM (a, FreeVars))
  -> RnM (a, FreeVars)
rnPats = rn_pats_general

rnPat
  :: forall a.
     BindKVs
  -> CsMatchContextRn
  -> LPat Ps
  -> (LPat Rn -> RnM (a, FreeVars))
  -> RnM (a, FreeVars)
rnPat = coerce (rn_pats_general @Identity @a)

applyNameMaker :: NameMaker -> LocatedN RdrName -> RnM (LocatedN Name)
applyNameMaker mk rdr = fst <$> runCps (newPatLName mk rdr)

{- *********************************************************************
*                                                                      *
              The main event
*                                                                      *
********************************************************************* -}

rnLArgPatAndThen :: BindKVs -> NameMaker -> LocatedA (Pat Ps) -> CpsRn (LocatedA (Pat Rn))
rnLArgPatAndThen bindkvs mk = wrapSrcSpanCps (rnPatAndThen bindkvs mk)

rnLPatsAndThen :: BindKVs -> NameMaker -> [LPat Ps] -> CpsRn [LPat Rn]
rnLPatsAndThen bindkvs mk = mapM (rnLPatAndThen bindkvs mk)

rnLPatAndThen :: BindKVs -> NameMaker -> LPat Ps -> CpsRn (LPat Rn)
rnLPatAndThen bindkvs nm lpat = wrapSrcSpanCps (rnPatAndThen bindkvs nm) lpat

rnPatAndThen :: BindKVs -> NameMaker -> Pat Ps -> CpsRn (Pat Rn)

rnPatAndThen _ _ (WildPat _) = return $ WildPat noExtField

rnPatAndThen _ mk (VarPat x (L l rdr)) = do
  loc <- liftCps getSrcSpanM
  name <- newPatName mk (L (noAnnSrcSpan loc) rdr)
  return $ VarPat x (L l name)

rnPatAndThen _ mk (TyVarPat x (L l rdr)) = do
  loc <- liftCps getSrcSpanM
  name <- newPatName mk (L (noAnnSrcSpan loc) rdr)
  return (TyVarPat x (L l name))

rnPatAndThen bindkvs mk (AsPat _ rdr pat) = do
  new_name <- newPatLName mk rdr
  pat' <- rnLPatAndThen bindkvs mk pat
  return $ AsPat noExtField new_name pat'

rnPatAndThen bindkvs mk (ParPat _ pat) = do
  pat' <- rnLPatAndThen bindkvs mk pat
  return $ ParPat noExtField pat'

rnPatAndThen bindkvs mk (TuplePat _ pats) = do
  pats' <- rnLPatsAndThen bindkvs mk pats
  return $ TuplePat noExtField pats'

rnPatAndThen bindkvs mk (SumPat _ pat alt arity) = do
  pat <- rnLPatAndThen bindkvs mk pat
  return $ SumPat noExtField pat alt arity

rnPatAndThen _ mk (ConPat _ con args) = rnConPatAndThen mk con args

rnPatAndThen _ mk (LitPat x lit) = do
  liftCps (rnLit lit)
  return (LitPat x (convertLit lit))

rnPatAndThen _ mk (NPat x (L l lit) mb_neg _) = do
  (lit', mb_neg') <- liftCpsFV $ rnOverLit lit
  mb_neg' <- let negative = do (neg, fvs) <- lookupSyntax negateName
                               return (Just neg, fvs)
                 positive = return (Nothing, emptyFVs)
             in liftCpsFV $ case (mb_neg, mb_neg') of
                              (Nothing, Just _) -> negative
                              (Just _, Nothing) -> negative
                              (Nothing, Nothing) -> positive
                              (Just _, Just _) -> positive
  return (NPat x (L l lit') mb_neg' noSyntaxExpr)

rnPatAndThen bindkvs mk (SigPat _ pat sig) = do
  sig' <- rnCsPatSigTypeAndThen sig -- binds implicit kvs. Could assert 'bindkvs == DoBindKVs'
  pat' <- rnLPatAndThen bindkvs mk pat
  return (SigPat noExtField pat' sig')
  where
    rnCsPatSigTypeAndThen :: CsPatSigType Ps -> CpsRn (CsPatSigType Rn)
    rnCsPatSigTypeAndThen sig = liftCpsWithCont (rnCsPatSigType PatCtx sig)

rnPatAndThen bindkvs mk (KdSigPat _ pat sig) = do
  sig' <- rnCsPatSigKindAndThen sig
  pat' <- rnLPatAndThen bindkvs mk pat
  return (KdSigPat noExtField pat' sig')
  where
    rnCsPatSigKindAndThen :: CsPatSigKind Ps -> CpsRn (CsPatSigKind Rn)
    rnCsPatSigKindAndThen sig = liftCpsWithCont (rnCsPatSigKind bindkvs PatCtx sig)

rnPatAndThen bindkvs mk (ImpPat _ pat) = do
  pat' <- rnLPatAndThen bindkvs mk pat
  return (ImpPat noExtField pat')

rnPatAndThen _ _ (XPat _) = panic "rnPatAndThen XPat"

rnConPatAndThen :: NameMaker -> LocatedN RdrName -> CsConPatDetails Ps -> CpsRn (Pat Rn)
rnConPatAndThen _ _ _ = panic "rnConPatAndThen"

{- *********************************************************************
*                                                                      *
              Literals
*                                                                      *
********************************************************************* -}

rnLit :: CsLit p -> RnM ()
rnLit (CsChar _ c) = checkErr (inCharRange c) (panic "TcRnCharLiteralOutOfRange c")
rnLit _ = panic "rnLit"

generalizeOverLitVal :: OverLitVal -> OverLitVal
generalizeOverLitVal (CsFractional fl@(FL { fl_text = src, fl_neg = neg, fl_exp = e }))
  | e >= -100 && e <= 100
  , let val = rationalFromFractionalLit fl
  , denominator val == 1
  = CsIntegral (IL { il_text = src, il_neg = neg, il_value = numerator val })
generalizeOverLitVal lit = lit

isNegativeZeroOverLit :: CsOverLit t -> Bool
isNegativeZeroOverLit lit = case ol_val lit of
  CsIntegral i -> 0 == il_value i && il_neg i
  CsFractional fl -> 0 == fl_signi fl && fl_neg fl
  _ -> False

csOverLitName :: OverLitVal -> Name
csOverLitName (CsIntegral {}) = panic "fromIntegerName"
csOverLitName (CsFractional {}) = panic "fromRationalName"
csOverLitName (CsIsString {}) = panic "fromStringName"

rnOverLit :: forall t. CsOverLit t -> RnM ((CsOverLit Rn, Maybe (CsExpr Rn)), FreeVars)
rnOverLit origLit = do
  let lit :: CsOverLit t
      lit@(OverLit { ol_val = val }) = origLit { ol_val = generalizeOverLitVal (ol_val origLit) }
      std_name = csOverLitName val
  (from_thing_name, fvs1) <- lookupSyntaxName std_name
  loc <- getSrcSpanM
  let lit' = lit { ol_ext = OverLitRn { ol_from_fun = L (noAnnSrcSpan loc) from_thing_name } }

  if isNegativeZeroOverLit lit'
    then do (negate_name, fvs2) <- lookupSyntaxExpr negateName
            return ( ( lit' { ol_val = negateOverLitVal val }
                     , Just negate_name )
                   , fvs1 `plusFV` fvs2 )
    else return ((lit', Nothing), fvs1)
