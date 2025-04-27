{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Parser.PostProcess
  ( SumOrTuple(..)

  , module CSlash.Parser.PostProcess
  ) where

import CSlash.Cs
import CSlash.Core.TyCon
import CSlash.Core.DataCon
import CSlash.Types.Name.Reader
import CSlash.Types.Name
import CSlash.Types.Basic
import CSlash.Types.Error
import CSlash.Types.Fixity
import CSlash.Types.Hint
import CSlash.Types.SourceText
import CSlash.Parser.Types
import CSlash.Parser.Lexer
import CSlash.Parser.Errors.Types
import CSlash.Parser.Errors.Ppr ()
import CSlash.Types.TyThing
import CSlash.Builtin.Types
import CSlash.Builtin.Types.Prim (fUNTyCon)
import CSlash.Types.SrcLoc
import CSlash.Types.Unique
import CSlash.Data.OrdList
import CSlash.Utils.Outputable as Outputable
import CSlash.Data.FastString
import CSlash.Data.Maybe
import CSlash.Utils.Error
import CSlash.Utils.Misc
import qualified Data.Semigroup as Semi
import CSlash.Utils.Panic
import qualified CSlash.Data.Strict as Strict

import Control.Monad
import qualified Data.Kind as K

{- **********************************************************************

  Construction functions for Rdr stuff

*********************************************************************** -}

mkKvRel :: SrcSpan -> LCsKind Ps -> LocatedN RdrName -> LCsKind Ps -> P (LCsKdRel Ps)
mkKvRel loc k1@(L l1 _) (L lr rel) k2@(L l2 _)
  | rdrNameOcc rel == mkUnknownOcc "<"
  = let cs = emptyComments Semi.<> comments l1 Semi.<> comments l2
        loc' = EpAnn (spanAsAnchor loc) noAnn cs
    in return $ L loc' (CsKdLT (EpTok $ entry lr) k1 k2)
  | rdrNameOcc rel == mkUnknownOcc "<="
  = let cs =  emptyComments Semi.<> comments l1 Semi.<> comments l2
        loc' = EpAnn (spanAsAnchor loc) noAnn cs
    in return $ L loc' (CsKdLTEQ (EpTok $ entry lr) k1 k2)
  | otherwise
  = addFatalError $ mkPlainErrorMsgEnvelope (locA lr) $ PsErrInvalidKindRelation rel

-- mkTySynonym in GHC
mkTyFunBind
  :: SrcSpan
  -> LocatedN RdrName
  -> LCsType Ps
  -> [AddEpAnn]
  -> P (LCsBind Ps)
mkTyFunBind loc name rhs annsIn = do
  cs <- checkTyHdr name
  let loc' = EpAnn (spanAsAnchor loc) noAnn cs
  return $ L loc' (TyFunBind annsIn name rhs)

-- mkFunBind
--   :: SrcSpan
--   -> Located RdrName
--   -> LCsExpr Ps
--   -> AddEpAnn
--   -> P (LCsBind Ps)
-- mkFunBind loc name rhs annsIn = return (L loc (VarBind annsIn name rhs))

fixValbindsAnn :: EpAnn AnnList -> EpAnn AnnList
fixValbindsAnn (EpAnn anchor (AnnList ma o c r t) cs)
  = (EpAnn (widenAnchor anchor (r ++ map trailingAnnToAddEpAnn t)) (AnnList ma o c r t) cs)

-- mkCsTyLamTy
--   :: SrcSpan
--   -> (LocatedL [LMatch Ps (LCsType Ps)])
--   -> [AddEpAnn]
--   -> P (LCsType Ps)
-- mkCsTyLamTy l (L lm m) anns = do
--   !cs <- getCommentsFor l
--   let mg = mkTyLamTyMatchGroup FromSource (L lm m)
--   checkTyLamTyMatchGroup l mg
--   return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsTyLamTy anns mg)

{- **********************************************************************

  Converting to CsBinds, etc.

*********************************************************************** -}

{- cvTopDecls

In GHC, this function looks for multiple definitions of the same function,
i.e., different patterns, and converts them from multiple declarations
to one function definition. Since we don't have this syntax,
we don't make this conversion.
Our syntax requires ALL declaration to be 'name = expr',
not 'name pats = expr'.
-}

cvBindGroup :: OrdList (LCsDecl Ps) -> P (CsValBinds Ps)
cvBindGroup binding = do
  (mbs, sigs) <- cvBindsAndSigs binding
  return $ ValBinds NoAnnSortKey mbs sigs

cvBindsAndSigs :: OrdList (LCsDecl Ps) -> P (LCsBinds Ps, [LSig Ps])
cvBindsAndSigs fb = return $ partitionBindsAndSigs $ fromOL fb

{- **********************************************************************

  Utilities for conversion

*********************************************************************** -}

-- GHC checkTyClHdr
checkTyHdr :: LocatedN RdrName -> P EpAnnComments
checkTyHdr ty@(L l name)
  | isRdrTyVar name = return $ emptyComments Semi.<> comments l
  | otherwise = addFatalError $ mkPlainErrorMsgEnvelope (locA l) $
                (PsErrMalformedTyDecl ty)

checkExpBlockArguments :: LCsExpr Ps -> PV ()
checkExpBlockArguments = checkExpr
  where
    checkExpr :: LCsExpr Ps -> PV ()
    checkExpr expr = case unLoc expr of
      CsCase {} -> check PsErrCaseInFunAppExpr expr
      CsLam {} -> check PsErrLambdaInFunAppExpr expr
      CsLet {} -> check PsErrLetInFunAppExpr expr
      CsIf {} -> check PsErrIfInFunAppExpr expr
      _ -> return ()
    check err a = addError $ mkPlainErrorMsgEnvelope (getLocA a) (err a)

checkTypeArguments :: LCsType Ps -> PV ()
checkTypeArguments ty = case unLoc ty of
  CsTyLamTy {} -> check PsErrLambdaInTyFunAppExpr ty
  _ -> return ()
  where
    check err a = addError $ mkPlainErrorMsgEnvelope (getLocA a) (err a)
      
-- -------------------------------------------------------------------------
-- Checking Patterns.

checkLArgListPat :: LocatedA (PatBuilder Ps) -> PV (LocatedA [LPat Ps])
checkLArgListPat (L l p) = case p of
  PatBuilderArgList ps -> (L l) <$> mapM checkLPat ps
  _ -> panic "checkLArgListPat"

checkLTyArgListPat :: LocatedA (TyPatBuilder Ps) -> PV (LocatedA [LPat Ps])
checkLTyArgListPat (L l p) = case p of
  TyPatBuilderArgList ps -> (L l) <$> mapM checkLTyPat ps
  _ -> panic "checkLTyArgListPat"

checkLTyPat :: LocatedA (TyPatBuilder Ps) -> PV (LPat Ps)
checkLTyPat (L l@(EpAnn anc an _) p) = do
  (L l' p', cs) <- checkTyPat (EpAnn anc an emptyComments) emptyComments (L l p)
  return (L (addCommentsToEpAnn l' cs) p')

checkTyPat
  :: SrcSpanAnnA -> EpAnnComments -> LocatedA (TyPatBuilder Ps) -> PV (LPat Ps, EpAnnComments)
checkTyPat loc cs (L l t) = do
  p <- checkATyPat loc t
  return (L l p, cs)

checkATyPat :: SrcSpanAnnA -> TyPatBuilder Ps -> PV (Pat Ps)
checkATyPat loc t0 =
  case t0 of
    TyPatBuilderPat p -> return p
    TyPatBuilderVar (L l v)
      | not (isRdrUnknown v) -> panic "checkATyPat1"
      | otherwise -> return (TyVarPat noExtField (L l (unknownToTv v)))
    TyPatBuilderPar lpar t rpar -> do
      p <- checkLTyPat t
      return (ParPat (lpar, rpar) p)
    _ -> do
      details <- fromParseContext <$> askParseContext
      patFail (locA loc) (PsErrInTyPat t0 details)

-- checkTyPattern :: Maybe (Located Token) -> LCsType Ps -> Maybe (Located Token) -> P (LPat Ps)
-- checkTyPattern moc (L l@(EpAnn anc an _) t) mcc = do
--   (L l' p, cs) <- checkTyPat (EpAnn anc an emptyComments) emptyComments moc (L l t) mcc
--   return (L (addCommentsToEpAnn l' cs) p)

-- checkTyPat
--   :: SrcSpanAnnA
--   -> EpAnnComments
--   -> Maybe (Located Token)
--   -> LCsType Ps
--   -> Maybe (Located Token)
--   -> P (LPat Ps, EpAnnComments)
-- checkTyPat loc cs moc ty mcc = case (moc, mcc) of
--   (Just oc, Just cc) -> do (p, cs') <- checkTyPat' loc cs ty
--                            let loc' = combineSrcSpans (getHasLoc oc) (getHasLoc cc)
--                                impPatAnn = EpAnnImpPat (EpTok $ EpaSpan $ getHasLoc oc)
--                                                        (EpTok $ EpaSpan $ getHasLoc cc)
--                            return ( L (EpAnn (spanAsAnchor loc') noAnn cs')
--                                       (ImpPat impPatAnn p)
--                                   , cs' )
--   (Nothing, Nothing) -> checkTyPat' loc cs ty
--   _ -> panic "checkTyPat"

-- checkTyPat'
--   :: SrcSpanAnnA
--   -> EpAnnComments
--   -> LCsType Ps
--   -> P (LPat Ps, EpAnnComments)
-- checkTyPat' loc cs (L l (CsTyVar an id))
--   = pure (L l (TyVarPat noExtField id), cs)
-- checkTyPat' loc cs (L l (CsParTy ann ty)) = do
--   p <- checkTyPattern Nothing ty Nothing
--   return (L l (ParPat ann p), cs)
-- checkTyPat' loc cs (L l (CsKindSig an ty kd)) = do
--   p <- checkVarTyPattern ty
--   return (L l (KdSigPat an p (CsPSK noAnn kd)), cs)
-- checkTyPat' loc _ ty
--   = addFatalError $ mkPlainErrorMsgEnvelope (locA loc) $ PsErrInTyPat (unLoc ty)

-- checkVarTyPattern :: LCsType Ps -> P (LPat Ps)
-- checkVarTyPattern (L l@(EpAnn anc an _) t) = do
--   (L l' p, cs) <- checkVarTyPat (EpAnn anc an emptyComments) emptyComments (L l t)
--   return (L (addCommentsToEpAnn l' cs) p)

-- checkVarTyPat
--   :: SrcSpanAnnA
--   -> EpAnnComments
--   -> LCsType Ps
--   -> P (LPat Ps, EpAnnComments)
-- checkVarTyPat loc cs (L l (CsTyVar an id)) = pure (L l (TyVarPat noExtField id), cs)
-- checkVarTyPat loc cs (L l (CsParTy ann ty)) = do
--   p <- checkVarTyPattern ty
--   return (L l (ParPat ann p), cs)
-- checkVarTyPat loc _ ty
--   = addFatalError $ mkPlainErrorMsgEnvelope (locA loc) $ PsErrInTyPat (unLoc ty)

-- new old
-- checkLTyPattern :: LocatedA (PatBuilder Ps) -> PV (LPat Ps)
-- checkLTyPattern (L l@(EpAnn anc an _) p) = do
--   (L l' p', cs) <- checkTyPat (EpAnn anc an emptyComments) emptyComments (L l p)
--   return (L (addCommentsToEpAnn l' cs) p')

-- checkTyPat
--   :: SrcSpanAnnA -> EpAnnComments -> LocatedA (PatBuilder Ps) -> PV (LPat Ps, EpAnnComments)
-- checkTyPat loc cs (L l t) = do
--   p <- checkATyPat loc t
--   return (L l p, cs)

-- checkATyPat :: SrcSpanAnnA -> PatBuilder Ps -> PV (Pat Ps)
-- checkATyPat loc t0 =
--   case t0 of
--     PatBuilderPat p -> return p
--     PatBuilderVar x -> return (TyVarPat noExtField x)
--     PatBuilderPar lpar t rpar -> do
--       p <- checkLTyPattern t
--       return (ParPat (lpar, rpar) p)
--     _ -> do
--       details <- fromParseContext <$> askParseContext
--       patFail (locA loc) (PsErrInTyPat t0 details)

checkPattern :: LocatedA (PatBuilder Ps) -> P (LPat Ps)
checkPattern = runPV . checkLPat

-- checkPattern_details :: ParseContext -> PV (LocatedA (PatBuilder Ps)) -> P (LPat Ps)
-- checkPattern_details extraDetails pp = runPV_details extraDetails (pp >>= checkLPat)

checkLPat :: LocatedA (PatBuilder Ps) -> PV (LPat Ps)
checkLPat (L l@(EpAnn anc an _) p) = do
  (L l' p', cs) <- checkPat (EpAnn anc an emptyComments) emptyComments (L l p) [] []
  return (L (addCommentsToEpAnn l' cs) p')

checkPat
  :: SrcSpanAnnA
  -> EpAnnComments
  -> LocatedA (PatBuilder Ps)
  -> [CsConPatTyArg Ps]
  -> [LPat Ps]
  -> PV (LPat Ps, EpAnnComments)
checkPat loc cs (L l e@(PatBuilderVar (L ln c))) tyargs args
  | not (isRdrUnknown c) = panic "checkPat1"
checkPat loc cs (L l e@(PatBuilderCon (L ln c))) tyargs args
  | not (isRdrUnknown c) = panic "checkPat2"
  | otherwise
  = return ( L loc $ ConPat
             { pat_con_ext = noAnn
             , pat_con = L ln (unknownToData c)
             , pat_args = PrefixCon tyargs args
             }
           , comments l Semi.<> cs )
checkPat loc cs (L la (PatBuilderAppType f t anns)) tyargs args =
  checkPat loc (cs Semi.<> comments la) f (CsConPatTyArg anns t : tyargs) args
checkPat loc cs (L la (PatBuilderApp f e)) [] args = do
  p <- checkLPat e
  checkPat loc (cs Semi.<> comments la) f [] (p : args)
checkPat loc cs (L l e) [] [] = do
  p <- checkAPat loc e
  return (L l p, cs)
checkPat loc _ e _ _ = do
  details <- fromParseContext <$> askParseContext
  patFail (locA loc) (PsErrInPat (unLoc e) details)

checkAPat :: SrcSpanAnnA -> PatBuilder Ps -> PV (Pat Ps)
checkAPat loc e0 = 
  case e0 of
    PatBuilderPat p -> return p
    PatBuilderVar (L l v)
      | not (isRdrUnknown v) -> panic "checkAPat1"
      | otherwise -> return (VarPat noExtField (L l (unknownToVar v)))
    PatBuilderOverLit pos_lit -> return (mkNPat (L (l2l loc) pos_lit) Nothing noAnn)
    PatBuilderOpApp _ op _ _
      | opIsAt (unLoc op) -> do
          addError $ mkPlainErrorMsgEnvelope (getLocA op) PsErrAtInPatPos
          return (WildPat noExtField)
    PatBuilderOpApp l (L cl c) r anns
      | not (isRdrUnknown c) -> panic "checkAPat2"
    PatBuilderConOpApp l (L cl c) r anns
      | not (isRdrUnknown c) -> panic "checkAPat3"
      | otherwise -> do
          l <- checkLPat l
          r <- checkLPat r
          return $ ConPat
            { pat_con_ext = anns
            , pat_con = L cl (unknownToData c)
            , pat_args = InfixCon l r
            }
    PatBuilderPar lpar e rpar -> do
      p <- checkLPat e
      return (ParPat (lpar, rpar) p)
    _ -> do
      details <- fromParseContext <$> askParseContext
      patFail (locA loc) (PsErrInPat e0 details)

patFail :: SrcSpan -> PsMessage -> PV a
patFail loc msg = addFatalError $ mkPlainErrorMsgEnvelope loc $ msg

---------------------------------------------------------------------------
-- Check Equation Syntax

-- renamed from GHC checkDoAndIfThenElse since we want to check this but
-- don't have do notation
checkLayoutIfThenElse
  :: (Outputable a, Outputable b, Outputable c)
  => (a -> Bool -> b -> Bool -> c -> PsMessage)
  -> LocatedA a
  -> Bool
  -> LocatedA b
  -> Bool
  -> LocatedA c
  -> PV ()
checkLayoutIfThenElse err guardExpr semiThen thenExpr semiElse elseExpr
  | semiThen || semiElse
  = let e = err (unLoc guardExpr) semiThen (unLoc thenExpr) semiElse (unLoc elseExpr)
        loc = combineLocs (reLoc guardExpr) (reLoc elseExpr)
    in addError (mkPlainErrorMsgEnvelope loc e)
  | otherwise = return ()

-- -------------------------------------------------------------------------
-- Expression/command/pattern ambiguity.

-- newtype ECP
--   = ECP { unECP :: forall b. DisambECP b => PV (LocatedA b) }

-- ecpFromExp :: LCsExpr Ps -> ECP
-- ecpFromExp a = ECP (ecpFromExp' a)

-- -- Currently NOT setting the namespace
-- class DisambInfixOp b where
--   mkCsVarOpPV :: LocatedN RdrName -> PV (LocatedN b)
--   mkCsConOpPV :: LocatedN RdrName -> PV (LocatedN b)

-- instance DisambInfixOp (CsExpr Ps) where
--   mkCsVarOpPV (L l rn) = assert (isRdrUnknown rn) $
--                          return $ L l (CsVar noExtField (L l rn))
--   mkCsConOpPV (L l rn) = assert (isRdrUnknown rn) $
--                          return $ L l (CsVar noExtField (L l rn))

-- instance DisambInfixOp RdrName where
--   mkCsVarOpPV (L l v) = assert (isRdrUnknown v) $
--                         return $ L l v
--   mkCsConOpPV (L l v) = assert (isRdrUnknown v) $
--                         return $ L l v

type AnnoBody b
  = ( Anno (GRHS Ps (LocatedA (Body b Ps))) ~ EpAnnCO
    , Anno [LocatedA (Match Ps (LocatedA (Body b Ps)))] ~ SrcSpanAnnL
    , Anno (Match Ps (LocatedA (Body b Ps))) ~ SrcSpanAnnA
    , Anno (StmtLR Ps Ps (LocatedA (Body (Body b Ps) Ps))) ~ SrcSpanAnnA
    , Anno [LocatedA (StmtLR Ps Ps
                      (LocatedA (Body (Body (Body b Ps) Ps) Ps)))] ~ SrcSpanAnnL
    )

newtype ETP = ETP { unETP :: forall b. DisambETP b => PV (LocatedA b) }

etpFromExp :: LCsExpr Ps -> ETP
etpFromExp a = ETP (etpFromExp' a)

etpFromTy :: LCsType Ps -> ETP
etpFromTy a = ETP (etpFromTy' a)

etpFromKd :: LCsKind Ps -> ETP
etpFromKd a = ETP (etpFromKd' a)

class (b ~ (Body b) Ps, AnnoBody b) => DisambETP b where
  type Body b :: K.Type -> K.Type
  etpFromExp' :: LCsExpr Ps -> PV (LocatedA b)
  etpFromTy' :: LCsType Ps -> PV (LocatedA b)
  etpFromKd' :: LCsKind Ps -> PV (LocatedA b)
  type SigTy b
  superSigPV :: (DisambETP (SigTy b) => PV (LocatedA b)) -> PV (LocatedA b)
  mkCsSigPV :: SrcSpanAnnA -> LocatedA b -> LocatedA (SigTy b) -> [AddEpAnn] -> PV (LocatedA b)
  mkCsOpAppPV :: SrcSpan -> LocatedA b -> LocatedN RdrName -> LocatedA b -> PV (LocatedA b)
  mkCsConOpAppPV :: SrcSpan -> LocatedA b -> LocatedN RdrName -> LocatedA b -> PV (LocatedA b)
  mkCsAppPV :: SrcSpanAnnA -> LocatedA b -> LocatedA b -> PV (LocatedA b)
  mkCsAsPatPV :: SrcSpan -> LocatedN RdrName -> EpToken "@" -> LocatedA b -> PV (LocatedA b)
  mkCsNegAppPV :: SrcSpan -> LocatedA b -> [AddEpAnn] -> PV (LocatedA b)
  mkCsLetPV
    :: SrcSpan
    -> EpToken "let"
    -> CsLocalBinds Ps
    -> EpToken "in"
    -> LocatedA b
    -> PV (LocatedA b)
  type ArgBuilder b
  superArgBuilderPV :: (DisambETP (ArgBuilder b) => PV (LocatedA b)) -> PV (LocatedA b)
  mkCsLamPV 
    :: SrcSpan
    -> LocatedA (ArgBuilder b)
    -> (CsMatchContext fn -> LocatedA [LPat Ps] -> LocatedL [LMatch Ps (LocatedA b)])
    -> [AddEpAnn]
    -> PV (LocatedA b)
  mkCsTyLamPV
    :: SrcSpan
    -> (LocatedL [LMatch Ps (LocatedA b)])
    -> [AddEpAnn]
    -> PV (LocatedA b)
  mkCsIfPV
    :: SrcSpan
    -> LCsExpr Ps
    -> Bool        -- semicolon? (I.e., newline)
    -> LocatedA b
    -> Bool        -- semicolon? (I.e., newline)
    -> LocatedA b
    -> AnnsIf
    -> PV (LocatedA b)
  mkCsCasePV
    :: SrcSpan
    -> LCsExpr Ps
    -> (LocatedL [LMatch Ps (LocatedA b)])
    -> EpAnnCsCase
    -> PV (LocatedA b)
  mkCsVarPV :: LocatedN RdrName -> PV (LocatedA b)
  mkCsConPV :: LocatedN RdrName -> PV (LocatedA b)
  mkCsLitPV :: Located (CsLit Ps) -> PV (LocatedA b)
  mkCsOverLitPV :: LocatedAn a (CsOverLit Ps) -> PV (LocatedAn a b)
  mkCsParPV :: SrcSpan -> EpToken "(" -> LocatedA b -> EpToken ")" -> PV (LocatedA b)
  mkCsSumOrTuplePV :: SrcSpanAnnA -> SumOrTuple b -> [AddEpAnn] -> PV (LocatedA b)
  mkCsWildCardPV :: (NoAnn a) => SrcSpan -> PV (LocatedAn a b)
  type InBraces b
  superBracesPV :: (DisambETP (InBraces b) => PV (LocatedA b)) -> PV (LocatedA b)
  mkCsInBracesPV :: SrcSpan -> LocatedA (InBraces b) -> [AddEpAnn] -> PV (LocatedA b)
  mkCsVarSectionL :: SrcSpan -> LocatedA b -> LocatedN RdrName -> PV (LocatedA b)
  mkCsConSectionL :: SrcSpan -> LocatedA b -> LocatedN RdrName -> PV (LocatedA b)
  mkCsVarSectionR :: SrcSpan -> LocatedN RdrName -> LocatedA b -> PV (LocatedA b)
  mkCsConSectionR :: SrcSpan -> LocatedN RdrName -> LocatedA b -> PV (LocatedA b)
  mkCsPatListPV :: LocatedA b -> PV (LocatedA b)
  mkCsPatListConsPV :: LocatedA b -> LocatedA b -> PV (LocatedA b)
  mkCsUnitSysConPV :: SrcSpan -> NameAnn -> PV (LocatedA b)
  mkCsTupleSysConPV :: SrcSpan -> NameAnn -> Int -> PV (LocatedA b)

instance DisambETP (CsExpr Ps) where
  type Body (CsExpr Ps) = CsExpr
  etpFromExp' = return
  etpFromTy' (L l t) = addFatalError $ mkPlainErrorMsgEnvelope (locA l) $ PsErrTypeInExpr t
  etpFromKd' (L l k) = addFatalError $ mkPlainErrorMsgEnvelope (locA l) $ PsErrKindInExpr k
  type SigTy (CsExpr Ps) = CsType Ps
  superSigPV e = e
  mkCsSigPV l@(EpAnn anc an csIn) e sig anns = do
    !cs <- getCommentsFor (locA l)
    return $ L (EpAnn anc an (csIn Semi.<> cs)) (ExprWithTySig anns e (csTypeToCsSigType sig))
  mkCsOpAppPV l e1 op@(L opl@(EpAnn anc _ _) n) e2 = do
    !vcs <- getCommentsFor (getHasLoc opl)
    massert (isRdrUnknown n)
    let nsOp = L opl (unknownToVar n)
        op' = L (EpAnn anc (noAnn :: NameAnn) vcs) (CsVar noExtField nsOp)
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) $ OpApp [] e1 (reLoc op') e2
  mkCsConOpAppPV l e1 op@(L opl@(EpAnn anc _ _) n) e2 = do
    !vcs <- getCommentsFor (getHasLoc opl)
    massert (isRdrUnknown n)
    let nsOp = L opl (unknownToData n)
        op' = L (EpAnn anc (noAnn :: NameAnn) vcs) (CsVar noExtField nsOp)
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) $ OpApp [] e1 (reLoc op') e2
  mkCsAppPV l e1 e2 = do
    checkExpBlockArguments e1
    checkExpBlockArguments e2
    return $ L l (CsApp noExtField e1 e2)
  mkCsAsPatPV l v _ e = addError (mkPlainErrorMsgEnvelope l PsErrUnexpectedAsPat)
                        >> return (L (noAnnSrcSpan l) (csHoleExpr noAnn))
  mkCsNegAppPV l a anns = do
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (NegApp anns a noSyntaxExpr)
  mkCsLetPV l tkLet bs tkIn c = do
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsLet (tkLet, tkIn) bs c)
  type ArgBuilder (CsExpr Ps) = PatBuilder Ps
  superArgBuilderPV e = e
  mkCsLamPV l pb mkMatch anns = do
    !cs <- getCommentsFor l
    p <- checkLArgListPat pb
    let m = mkMatch LamAlt p
        mg = mkLamMatchGroup FromSource m
    checkLamMatchGroup l mg
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsLam anns mg)
  mkCsTyLamPV l m anns = do
    !cs <- getCommentsFor l
    let mg = mkTyLamMatchGroup FromSource m
    checkTyLamMatchGroup l mg
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsTyLam anns mg)
  mkCsIfPV l c semi1 a semi2 b anns = do
    checkLayoutIfThenElse PsErrSemiColonsInCondExpr c semi1 a semi2 b
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (mkCsIf c a b anns)
  mkCsCasePV l e m anns = do
    !cs <- getCommentsFor l
    let mg = mkMatchGroup FromSource m
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsCase anns e mg)
  mkCsVarPV v@(L l@(EpAnn anc _ _) n) = do
    !cs <- getCommentsFor (getHasLoc l)
    massert (isRdrUnknown n)
    let v' = L l (unknownToVar n)
    return $ L (EpAnn anc noAnn cs) (CsVar noExtField v')
  mkCsConPV v@(L l@(EpAnn anc _ _) n) = do
    !cs <- getCommentsFor (getHasLoc l)
    massert (isRdrUnknown n)
    let v' = L l (unknownToData n)
    return $ L (EpAnn anc noAnn cs) (CsVar noExtField v')
  mkCsLitPV (L l a) = do
    !cs <- getCommentsFor (getHasLoc l)
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsLit noExtField a)
  mkCsOverLitPV (L (EpAnn l an csIn) a) = do
    !cs <- getCommentsFor (locA l)
    return $ L (EpAnn l an (cs Semi.<> csIn)) (CsOverLit noExtField a)
  mkCsParPV l lpar e rpar = do
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsPar (lpar, rpar) e)
  mkCsSumOrTuplePV = mkSumOrTupleExpr
  mkCsWildCardPV l = return $ L (noAnnSrcSpan l) (csHoleExpr noAnn)
  type InBraces (CsExpr Ps) = CsType Ps
  superBracesPV e = e
  mkCsInBracesPV l ty anns = do
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsEmbTy anns ty)
  mkCsVarSectionL l e op@(L opl@(EpAnn anc _ _) n) = do
    !opcs <- getCommentsFor (getHasLoc opl)
    massert (isRdrUnknown n)
    let op' = L opl (unknownToVar n)
        eop = L (EpAnn anc noAnn opcs) (CsVar noExtField op')
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (SectionL noExtField e eop)
  mkCsConSectionL l e op@(L opl@(EpAnn anc _ _) n) = do
    !opcs <- getCommentsFor (getHasLoc opl)
    massert (isRdrUnknown n)
    let op' = L opl (unknownToData n)
        eop = L (EpAnn anc noAnn opcs) (CsVar noExtField op')
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (SectionL noExtField e eop)
  mkCsVarSectionR l op@(L opl@(EpAnn anc _ _)n) e = do
    !opcs <- getCommentsFor (getHasLoc opl)
    massert (isRdrUnknown n)
    let op' = L opl (unknownToVar n)
        eop = L (EpAnn anc noAnn opcs) (CsVar noExtField op')
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (SectionR noExtField eop e)
  mkCsConSectionR l op@(L opl@(EpAnn anc _ _) n) e = do
    !opcs <- getCommentsFor (getHasLoc opl)
    massert (isRdrUnknown n)
    let op' = L opl (unknownToData n)
        eop = L (EpAnn anc noAnn opcs) (CsVar noExtField op')
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (SectionR noExtField eop e)
  mkCsPatListPV _ = panic "mkCsPatListPV expr"
  mkCsPatListConsPV _ _ = panic "mkCsPatListConsPV expr"
  mkCsUnitSysConPV l an = do
    !cs <- getCommentsFor l
    let rdrName = nameRdrName unitDataConName
        lrdrName = L (EpAnn (spanAsAnchor l) an cs) rdrName
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsVar noExtField lrdrName)
  mkCsTupleSysConPV l an arity = do
    !cs <- getCommentsFor l
    let rdrName = nameRdrName $ tupleDataConName arity
        lrdrName = L (EpAnn (spanAsAnchor l) an cs) rdrName
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsVar noExtField lrdrName)

instance DisambETP (CsType Ps) where
  type Body (CsType Ps) = CsType
  etpFromExp' (L l e) = addFatalError $ mkPlainErrorMsgEnvelope (locA l) $ PsErrExpInType e
  etpFromTy' = return
  etpFromKd' (L l e) = addFatalError $ mkPlainErrorMsgEnvelope (locA l) $ PsErrKindInType e
  type SigTy (CsType Ps) = CsKind Ps
  superSigPV t = t
  mkCsSigPV l@(EpAnn anc an csIn) t k anns = do
    !cs <- getCommentsFor (locA l)
    return $ L (EpAnn anc an (csIn Semi.<> cs)) (CsKindSig anns t k)
  mkCsOpAppPV l t1 (L opl n) t2 = do
    massert (isRdrUnknown n)
    let op = L opl (unknownToTv n)
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsOpTy [] t1 op t2)
  mkCsConOpAppPV l t1 (L opl n) t2 = do
    massert (isRdrUnknown n)
    let op = L opl (unknownToTcCls n)
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsOpTy [] t1 op t2)
  mkCsAppPV l t1 t2 = do
    checkTypeArguments t1
    checkTypeArguments t2
    return $ L l (CsAppTy noExtField t1 t2)
  mkCsAsPatPV l v _ e = addError (mkPlainErrorMsgEnvelope l PsErrUnexpectedAsPat)
                        >> return (L (noAnnSrcSpan l) (csHoleType noAnn))
  mkCsNegAppPV l _ _= addFatalError $ mkPlainErrorMsgEnvelope l PsErrNegAppInType
  mkCsLetPV l _ _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrLetInType
  type ArgBuilder (CsType Ps) = TyPatBuilder Ps
  superArgBuilderPV t = t
  mkCsLamPV l tpb mkMatch anns = do
    !cs <- getCommentsFor l
    tp <- checkLTyArgListPat tpb
    let m = mkMatch TyLamTyAlt tp
        mg = mkTyLamTyMatchGroup FromSource m
    checkTyLamTyMatchGroup l mg
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsTyLamTy anns mg)
  mkCsTyLamPV l _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrTyLamInType
  mkCsIfPV l _ _ _ _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrIfInType
  mkCsCasePV l _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrCaseInType
  mkCsVarPV v@(L l@(EpAnn anc _ _) n) = do
    !cs <- getCommentsFor (getHasLoc l)
    massert (isRdrUnknown n)
    let v' = L l (unknownToTv n)
    return $ L (EpAnn anc noAnn cs) (CsTyVar [] v')
  mkCsConPV v@(L l@(EpAnn anc _ _) n) = do
    !cs <- getCommentsFor (getHasLoc l)
    massert (isRdrUnknown n)
    let v' = L l (unknownToTcCls n)
    return $ L (EpAnn anc noAnn cs) (CsTyVar [] v')
  mkCsLitPV (L l _) = addFatalError $ mkPlainErrorMsgEnvelope (locA l) PsErrLitInType
  mkCsOverLitPV (L l _) = addFatalError $ mkPlainErrorMsgEnvelope (locA l) PsErrOverLitInType
  mkCsParPV l lpar t rpar = do
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsParTy (lpar, rpar) t)
  mkCsSumOrTuplePV = mkSumOrTupleType
  mkCsWildCardPV l = return $ L (noAnnSrcSpan l) (csHoleType noAnn)
  type InBraces (CsType Ps) = CsType Ps
  superBracesPV t = t
  mkCsInBracesPV l _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrInBracesType
  mkCsVarSectionL l t op@(L opl@(EpAnn anc _ _) n) = do
    !opcs <- getCommentsFor (getHasLoc l)
    massert (isRdrUnknown n)
    let op' = L opl (unknownToTv n)
        top = L (EpAnn anc noAnn opcs) (CsTyVar [] op')
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (TySectionL noExtField t top)
  mkCsConSectionL l t op@(L opl@(EpAnn anc _ _) n) = do
    !opcs <- getCommentsFor (getHasLoc opl)
    massert (isRdrUnknown n)
    let op' = L opl (unknownToTcCls n)
        top = L (EpAnn anc noAnn opcs) (CsTyVar [] op')
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (TySectionL noExtField t top)
  mkCsVarSectionR l op@(L opl@(EpAnn anc _ _) n) t = do
    !opcs <- getCommentsFor (getHasLoc l)
    massert (isRdrUnknown n)
    let op' = L opl (unknownToTv n)
        top = L (EpAnn anc noAnn opcs) (CsTyVar [] op')
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (TySectionR noExtField top t)
  mkCsConSectionR l op@(L opl@(EpAnn anc _ _) n) t = do
    !opcs <- getCommentsFor (getHasLoc opl)
    massert (isRdrUnknown n)
    let op' = L opl (unknownToTcCls n)
        top = L (EpAnn anc noAnn opcs) (CsTyVar [] op')
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (TySectionL noExtField top t)
  mkCsPatListPV _ = panic "mkCsPatListPV type"
  mkCsPatListConsPV _ _ = panic "mkCsPatListConsPV type"
  mkCsUnitSysConPV l an = do
    !cs <- getCommentsFor l
    let rdrName = nameRdrName unitTyConName
        lrdrName = L (EpAnn (spanAsAnchor l) an cs) rdrName
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsTyVar [] lrdrName)
  mkCsTupleSysConPV l an arity = do
    !cs <- getCommentsFor l
    let rdrName = nameRdrName $ tupleTyConName arity
        lrdrName = L (EpAnn (spanAsAnchor l) an cs) rdrName
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsTyVar [] lrdrName)
    
instance DisambETP (CsKind Ps) where
  type Body (CsKind Ps) = CsKind
  etpFromExp' (L l e) = addFatalError $ mkPlainErrorMsgEnvelope (locA l) $ PsErrExpInKind e
  etpFromTy' (L l t) = addFatalError $ mkPlainErrorMsgEnvelope (locA l) $ PsErrTypeInKind t
  etpFromKd' = return
  type SigTy (CsKind Ps) = CsKind Ps
  superSigPV k = k
  mkCsSigPV l _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope (locA l) PsErrKindWithSig
  mkCsOpAppPV l _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrKindOpApp
  mkCsConOpAppPV l _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrKindOpApp
  mkCsAppPV l _ _ = addFatalError $ mkPlainErrorMsgEnvelope (locA l) PsErrKindApp
  mkCsAsPatPV l _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrUnexpectedAsPat
  mkCsNegAppPV l _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrNegAppInKind
  mkCsLetPV l _ _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrLetInKind
  type ArgBuilder (CsKind Ps) = PatBuilder Ps
  superArgBuilderPV k = k
  mkCsLamPV l _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrLamInKind
  mkCsTyLamPV l _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrTyLamInKind
  mkCsIfPV l _ _ _ _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrIfInKind
  mkCsCasePV l _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrCaseInKind
  mkCsVarPV v@(L l@(EpAnn anc _ _) n) = do
    !cs <- getCommentsFor (getHasLoc l)
    massert (isRdrUnknown n)
    let v' = L l (unknownToKv n)
    return $ L (EpAnn anc noAnn cs) (CsKdVar [] v')
  mkCsConPV (L l _) = addFatalError $ mkPlainErrorMsgEnvelope (locA l) PsErrKindCon
  mkCsLitPV (L l _) = addFatalError $ mkPlainErrorMsgEnvelope (locA l) PsErrLitInKind
  mkCsOverLitPV (L l _) = addFatalError $ mkPlainErrorMsgEnvelope (locA l) PsErrOverLitInKind
  mkCsParPV l lpar k rpar = do
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsParKd (lpar, rpar) k)
  mkCsSumOrTuplePV l _ _ = addFatalError $ mkPlainErrorMsgEnvelope (locA l) PsErrSumOrTupleKind
  mkCsWildCardPV l = addFatalError $ mkPlainErrorMsgEnvelope l PsErrWildCardKind
  type InBraces (CsKind Ps) = CsType Ps
  superBracesPV k = k
  mkCsInBracesPV l _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrInBracesKind
  mkCsVarSectionL l _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrKindSection
  mkCsConSectionL l _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrKindSection
  mkCsVarSectionR l _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrKindSection
  mkCsConSectionR l _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrKindSection
  mkCsPatListPV _ = panic "mkCsPatListPV kind"
  mkCsPatListConsPV _ _ = panic "mkCsPatListConsPV kind"
  mkCsUnitSysConPV _ _ = panic "mkCsUnitSysConPV kind"
  mkCsTupleSysConPV _ _ _ = panic "mkCsTupleSysConPV kind"

-- We don't set RdrName namespaces here:
-- PatBuilder is used to build argument patterns for term and type level lambdas.
-- The DisambETP instances for Expr and Type should set RdrName namespaces;
-- probably in 'mkLamMatchGroup' and others
instance DisambETP (PatBuilder Ps) where
  type Body (PatBuilder Ps) = PatBuilder
  etpFromExp' (L l e) = addFatalError $ mkPlainErrorMsgEnvelope (locA l) $ PsErrArrowExprInPat e
  etpFromTy' (L l t) = addFatalError $ mkPlainErrorMsgEnvelope (locA l) $ PsErrTypeInPat t
  etpFromKd' (L l k) = addFatalError $ mkPlainErrorMsgEnvelope (locA l) $ PsErrKindInPat k
  type SigTy (PatBuilder Ps) = CsType Ps
  superSigPV p = p
  mkCsSigPV l b sig anns = do
    p <- checkLPat b
    return $ L l (PatBuilderPat (SigPat anns p (mkCsPatSigType noAnn sig)))
  mkCsOpAppPV l p1 op p2 = do
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) $ PatBuilderOpApp p1 op p2 []
  mkCsConOpAppPV l p1 op p2 = do
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) $ PatBuilderConOpApp p1 op p2 []
  mkCsAppPV l p1 p2 = return $ L l (PatBuilderApp p1 p2)
  mkCsAsPatPV l v at e = do
    p <- checkLPat e
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (PatBuilderPat (AsPat at v p))
  mkCsNegAppPV l (L lp p) anns = do
    lit <- case p of
             PatBuilderOverLit pos_lit -> return (L (l2l lp) pos_lit)
             _ -> patFail l $ PsErrInPat p PEIP_NegApp
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs)
               (PatBuilderPat (mkNPat lit (Just noSyntaxExpr) anns))
  mkCsLetPV l _ _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrLetInPat
  type ArgBuilder (PatBuilder Ps) = PatBuilder Ps
  superArgBuilderPV p = p
  mkCsLamPV l _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrLambdaInPat
  mkCsTyLamPV l _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrTyLambdaInPat
  mkCsIfPV l _ _ _ _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrIfInPat
  mkCsCasePV l _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrCaseInPat
  mkCsVarPV v@(L l _) = return $ L (l2l l) (PatBuilderVar v)
  mkCsConPV v@(L l _) = return $ L (l2l l) (PatBuilderCon v)
  mkCsLitPV lit@(L l a) = do
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (PatBuilderPat (LitPat noExtField a))
  mkCsOverLitPV (L l a) = return $ L l (PatBuilderOverLit a)
  mkCsParPV l lpar p rpar = return $ L (noAnnSrcSpan l) (PatBuilderPar lpar p rpar)
  mkCsSumOrTuplePV = mkSumOrTuplePat
  mkCsWildCardPV l = return $ L (noAnnSrcSpan l) (PatBuilderPat (WildPat noExtField))
  type InBraces (PatBuilder Ps) = PatBuilder Ps
  superBracesPV p = p
  mkCsInBracesPV l p anns = do panic "mkCsInBracesPV PatBuilder"
    -- !cs <- getCommentsFor l
    -- let impAnn = case anns of
    --                [AddEpAnn AnnOpenC ol, AddEpAnn AnnCloseC cl] ->
    --                  EpAnnImpPat (EpTok ol) (EpTok cl)
    --                _ -> panic "mkCsInBracesPV(PatBuilder) bad anns"
    -- pat <- checkLImpTyPat p
    -- return $ L (EpAnn (spanAsAnchor l) noAnn cs) (PatBuilderPat (ImpPat impAnn pat))
  mkCsVarSectionL l p op = patFail l (PsErrParseLeftOpSectionInPat (Left $ unLoc p) (unLoc op))
  mkCsConSectionL l p op = patFail l (PsErrParseLeftOpSectionInPat (Left $ unLoc p) (unLoc op))
  mkCsVarSectionR l op p = patFail l (PsErrParseRightOpSectionInPat (unLoc op) (Left $ unLoc p))
  mkCsConSectionR l op p = patFail l (PsErrParseRightOpSectionInPat (unLoc op) (Left $ unLoc p))
  mkCsPatListPV p@(L l _) = return $ L l $ PatBuilderArgList [p]
  mkCsPatListConsPV lp0@(L _ p0) lp = case p0 of
    PatBuilderArgList lps -> let lps' = lps ++ [lp]
                            in return $ addCLocA lp0 lp $ PatBuilderArgList lps'
    _ -> panic "mkCsPatListConsPV PB not list"
  mkCsUnitSysConPV l an = do
    !cs <- getCommentsFor l
    let rdrName = nameRdrName unitDataConName
        v@(L l' _) = L (EpAnn (spanAsAnchor l) an cs) rdrName
    return $ L (l2l l') (PatBuilderCon v)
  mkCsTupleSysConPV l an arity = do
    !cs <- getCommentsFor l
    let rdrName = nameRdrName $ tupleDataConName arity
        v@(L l' _) = L (EpAnn (spanAsAnchor l) an cs) rdrName
    return $ L (l2l l') (PatBuilderCon v)

instance DisambETP (TyPatBuilder Ps) where
  type Body (TyPatBuilder Ps) = TyPatBuilder
  etpFromExp' (L l e) = addFatalError $ mkPlainErrorMsgEnvelope (locA l) $ PsErrArrowExprInPat e
  etpFromTy' (L l t) = addFatalError $ mkPlainErrorMsgEnvelope (locA l) $ PsErrTypeInPat t
  etpFromKd' (L l k) = addFatalError $ mkPlainErrorMsgEnvelope (locA l) $ PsErrKindInPat k
  type SigTy (TyPatBuilder Ps) = CsKind Ps
  superSigPV p = p
  mkCsSigPV l b sig anns = do
    p <- checkLTyPat b
    return $ L l (TyPatBuilderPat (KdSigPat anns p (mkCsPatSigKind noAnn sig)))
  mkCsOpAppPV l p1 op p2 = do
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) $ TyPatBuilderOpApp p1 op p2 []
  mkCsConOpAppPV l p1 op p2 = do
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) $ TyPatBuilderConOpApp p1 op p2 []
  mkCsAppPV l p1 p2 = return $ L l (TyPatBuilderApp p1 p2)
  mkCsAsPatPV l _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrUnexpectedAsPat
  mkCsNegAppPV l _ _= addFatalError $ mkPlainErrorMsgEnvelope l PsErrNegAppInType
  mkCsLetPV l _ _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrLetInPat
  type ArgBuilder (TyPatBuilder Ps) = TyPatBuilder Ps
  superArgBuilderPV p = p
  mkCsLamPV l _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrLambdaInPat
  mkCsTyLamPV l _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrTyLambdaInPat
  mkCsIfPV l _ _ _ _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrIfInPat
  mkCsCasePV l _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrCaseInPat
  mkCsVarPV v@(L l _) = return $ L (l2l l) (TyPatBuilderVar v)
  mkCsConPV v@(L l _) = return $ L (l2l l) (TyPatBuilderCon v)
  mkCsLitPV (L l _) = addFatalError $ mkPlainErrorMsgEnvelope (locA l) PsErrLitInType
  mkCsOverLitPV (L l _) = addFatalError $ mkPlainErrorMsgEnvelope (locA l) PsErrOverLitInType
  mkCsParPV l lpar p rpar = return $ L (noAnnSrcSpan l) (TyPatBuilderPar lpar p rpar)
  mkCsSumOrTuplePV _ _ _ = panic "mkCsSumOrTuplePV TPB"
  mkCsWildCardPV l = return $ L (noAnnSrcSpan l) (TyPatBuilderPat (WildPat noExtField))
  type InBraces (TyPatBuilder Ps) = TyPatBuilder Ps
  superBracesPV p = p
  mkCsInBracesPV l p anns = do
    !cs <- getCommentsFor l
    let impAnn = case anns of
                   [AddEpAnn AnnOpenC ol, AddEpAnn AnnCloseC cl] ->
                     EpAnnImpPat (EpTok ol) (EpTok cl)
                   _ -> panic "mkCsInBracesPV(PatBuilder) bad anns"
    pat <- checkLTyPat p
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (TyPatBuilderPat (ImpPat impAnn pat))
  mkCsVarSectionL l p op = patFail l (PsErrParseLeftOpSectionInPat (Right $ unLoc p) (unLoc op))
  mkCsConSectionL l p op = patFail l (PsErrParseLeftOpSectionInPat (Right $ unLoc p) (unLoc op))
  mkCsVarSectionR l op p = patFail l (PsErrParseRightOpSectionInPat (unLoc op) (Right $ unLoc p))
  mkCsConSectionR l op p = patFail l (PsErrParseRightOpSectionInPat (unLoc op) (Right $ unLoc p))
  mkCsPatListPV p@(L l _) = return $ L l $ TyPatBuilderArgList [p]
  mkCsPatListConsPV lp0@(L _ p0) lp = case p0 of
    TyPatBuilderArgList lps -> let lps' = lps ++ [lp]
                              in return $ addCLocA lp0 lp $ TyPatBuilderArgList lps'
    _ -> panic "mkCsPatListConsPV TPB not list"
  mkCsUnitSysConPV l an = do
    !cs <- getCommentsFor l
    let rdrName = nameRdrName unitTyConName
        v@(L l' _) = L (EpAnn (spanAsAnchor l) an cs) rdrName
    return $ L (l2l l') (TyPatBuilderCon v)
  mkCsTupleSysConPV l an arity = do
    !cs <- getCommentsFor l
    let rdrName = nameRdrName $ tupleTyConName arity
        v@(L l' _) = L (EpAnn (spanAsAnchor l) an cs) rdrName
    return $ L (l2l l') (TyPatBuilderCon v)
  
checkLamMatchGroup :: SrcSpan -> MatchGroup Ps (LCsExpr Ps) -> PV ()
checkLamMatchGroup l (MG { mg_alts = (L _ (matches:_)) }) = do
  when (null (csLMatchPats matches)) $ addError $ mkPlainErrorMsgEnvelope l PsErrEmptyLambda
checkLamMatchGroup _ _ = panic "checkLamMatchGroup"

checkTyLamMatchGroup :: SrcSpan -> MatchGroup Ps (LCsExpr Ps) -> PV ()
checkTyLamMatchGroup l (MG { mg_alts = (L _ (matches:_)) }) = do
  when (null (csLMatchPats matches)) $ addError $ mkPlainErrorMsgEnvelope l PsErrEmptyTyLam
checkTyLamMatchGroup _ _ = panic "checkTyLamMatchGroup"

checkTyLamTyMatchGroup :: SrcSpan -> MatchGroup Ps (LCsType Ps) -> PV ()
checkTyLamTyMatchGroup l (MG { mg_alts = (L _ (matches:_)) }) = do
  when (null (csLMatchPats matches)) $ addError $ mkPlainErrorMsgEnvelope l PsErrEmptyTyLamTy
checkTyLamTyMatchGroup _ _ = panic "checkTyLamTyMatchGroup"

csHoleExpr :: Maybe EpAnnUnboundVar -> CsExpr Ps
csHoleExpr anns = CsUnboundVar anns (mkRdrUnqual (mkVarOccFS (fsLit "_")))

csHoleType :: Maybe EpAnnUnboundTyVar -> CsType Ps
csHoleType anns = CsUnboundTyVar anns (mkRdrUnqual (mkTyVarOccFS (fsLit "_")))


class DisambTD b where
  mkCsAppTyHeadPV :: LCsType Ps -> PV (LocatedA b)
  mkCsAppTyPV :: LocatedA b -> LCsType Ps -> PV (LocatedA b)
  mkCsOpTyPV :: LCsType Ps -> LocatedN RdrName -> LCsType Ps -> PV (LocatedA b)

instance DisambTD (CsType Ps) where
  mkCsAppTyHeadPV = return
  mkCsAppTyPV t1 t2 = return (mkCsAppTy t1 t2)
  mkCsOpTyPV t1 op t2 = do
    let (L l ty) = mkLCsOpTy t1 op t2
    !cs <- getCommentsFor (locA l)
    return $ L (addCommentsToEpAnn l cs) ty

---------------------------------------------------------------------------
-- Miscellaneous utilities

checkPrecP
  :: Located (SourceText, Int)
  -> LocatedN RdrName
  -> P ()
checkPrecP (L l (_, i)) op
  | 0 <= i, i <= maxPrecedence = pure ()
  | specialOp op = pure ()
  | otherwise = addFatalError $ mkPlainErrorMsgEnvelope l (PsErrPrecedenceOutOfRange i)
  where
    specialOp op = unLoc op == getRdrName fUNTyCon

--------------------------------------------------------------------------------
-- Help with module system imports/exports

data ImpExpSubSpec = ImpExpAbs

data ImpExpQcSpec = ImpExpQcName (LocatedN RdrName)
                  | ImpExpQcTyVar EpaLocation (LocatedN RdrName)

mkModuleImpExp :: [AddEpAnn] -> LocatedA ImpExpQcSpec -> ImpExpSubSpec -> P (IE Ps)
mkModuleImpExp anns (L l specname) subs = do
  case subs of
    ImpExpAbs
      | isVarNameSpace (rdrNameSpace name)
        -> return $ IEVar noExtField (L l (ieNameFromSpec specname))
      | isTvNameSpace (rdrNameSpace name)
        -> return $ IEVar noExtField (L l (ieNameFromSpec specname))
      | otherwise -> panic "mkModuleImpExp"
  where
    name = ieNameVal specname

    ieNameVal (ImpExpQcName ln) = unLoc ln
    ieNameVal (ImpExpQcTyVar _ ln) = unLoc ln

    ieNameFromSpec :: ImpExpQcSpec -> IEWrappedName Ps
    ieNameFromSpec (ImpExpQcName (L l n)) = IEName noExtField (L l n)
    ieNameFromSpec (ImpExpQcTyVar r (L l n)) = IETyName r (L l n)

-- forward compatability:
-- checks that imports of the form 'Thing(Thing1, Thing2, ..)'
-- are handled properly
checkImportSpec :: LocatedL [LIE Ps] -> P (LocatedL [LIE Ps])
checkImportSpec = pure

-----------------------------------------------------------------------------
-- Warnings and failures

failOpFewArgs :: MonadP m => LocatedN RdrName -> m a
failOpFewArgs (L loc op) = addFatalError $ mkPlainErrorMsgEnvelope (locA loc)
                                             (PsErrOpFewArgs op)

-----------------------------------------------------------------------------
-- Misc utils

data PV_Context = PV_Context
  { pv_options :: ParserOpts
  , pv_details :: ParseContext
  }

data PV_Accum = PV_Accum
  { pv_warnings :: Messages PsMessage
  , pv_errors :: Messages PsMessage
  , pv_header_comments :: Strict.Maybe [LEpaComment]
  , pv_comment_q :: [LEpaComment]
  }

data PV_Result a = PV_Ok PV_Accum a | PV_Failed PV_Accum
  deriving (Foldable, Functor, Traversable)

newtype PV a = PV { unPV :: PV_Context -> PV_Accum -> PV_Result a }
  deriving (Functor)

instance Applicative PV where
  pure a = a `seq` PV (\ _ acc -> PV_Ok acc a)
  (<*>) = ap

instance Monad PV where
  m >>= f = PV $ \ ctx acc ->
    case unPV m ctx acc of
      PV_Ok acc' a -> unPV (f a) ctx acc'
      PV_Failed acc' -> PV_Failed acc'

runPV :: PV a -> P a
runPV = runPV_details noParseContext

askParseContext :: PV ParseContext
askParseContext = PV $ \(PV_Context _ details) acc -> PV_Ok acc details

runPV_details :: ParseContext -> PV a -> P a
runPV_details details m =
  P $ \ s ->
        let pv_ctx = PV_Context
              { pv_options = options s
              , pv_details = details
              }
            pv_acc = PV_Accum
              { pv_warnings = warnings s
              , pv_errors = errors s
              , pv_header_comments = header_comments s
              , pv_comment_q = comment_q s
              }
            mkPState acc' = s
              { warnings = pv_warnings acc'
              , errors = pv_errors acc'
              , comment_q = pv_comment_q acc'
              }
        in case unPV m pv_ctx pv_acc of
             PV_Ok acc' a -> POk (mkPState acc') a
             PV_Failed acc' -> PFailed (mkPState acc')

instance MonadP PV where
  addError err =
    PV $ \ _ctx acc -> PV_Ok acc{ pv_errors = err `addMessage` pv_errors acc } ()
  addWarning w =
    PV $ \ _ctx acc -> PV_Ok acc{ pv_warnings = w `addMessage` pv_warnings acc } ()
  addFatalError err =
    addError err >> PV (const PV_Failed)
  allocateCommentsP ss = PV $ \ _ s ->
    if null (pv_comment_q s)
    then PV_Ok s emptyComments
    else let (comment_q', newAnns) = allocateComments ss (pv_comment_q s)
         in PV_Ok s{ pv_comment_q = comment_q' } (EpaComments newAnns)
  allocatePriorCommentsP ss = PV $ \ _ s ->
    let (header_comments', comment_q', newAnns)
          = allocatePriorComments ss (pv_comment_q s) (pv_header_comments s)
    in PV_Ok s{ pv_header_comments = header_comments'
              , pv_comment_q = comment_q' } (EpaComments newAnns)
  allocateFinalCommentsP ss = PV $ \ _ s ->
    let (header_comments', comment_q', newAnns)
          = allocateFinalComments ss (pv_comment_q s) (pv_header_comments s)
    in PV_Ok s{ pv_header_comments = header_comments'
              , pv_comment_q = comment_q' }
       (EpaCommentsBalanced (Strict.fromMaybe [] header_comments') newAnns)

mkSumOrTupleExpr :: SrcSpanAnnA -> SumOrTuple (CsExpr Ps) -> [AddEpAnn] -> PV (LCsExpr Ps)
mkSumOrTupleExpr l@(EpAnn anc an csIn) (Tuple es) anns = do
    !cs <- getCommentsFor (locA l)
    return $ L (EpAnn anc an (csIn Semi.<> cs)) (ExplicitTuple anns (map toTupArg es))
  where
    toTupArg :: Either (EpAnn Bool) (LCsExpr Ps) -> CsTupArg Ps
    toTupArg (Left ann) = missingTupArg ann
    toTupArg (Right a) = Present noExtField a
mkSumOrTupleExpr l@(EpAnn anc anIn csIn) (Sum alt arity e barsp barsa) anns = do
  let an = case anns of
             [AddEpAnn AnnOpenP o, AddEpAnn AnnCloseP c] ->
               AnnExplicitSum o barsp barsa c
             _ -> panic "mkSumOrTupleExpr"
  !cs <- getCommentsFor (locA l)
  return $ L (EpAnn anc anIn (csIn Semi.<> cs)) (ExplicitSum an alt arity e)

mkSumOrTupleType :: SrcSpanAnnA -> SumOrTuple (CsType Ps) -> [AddEpAnn] -> PV (LCsType Ps)
mkSumOrTupleType l@(EpAnn anc an csIn) (Tuple ts) anns = do
  !cs <- getCommentsFor (locA l)
  return $ L (EpAnn anc an (csIn Semi.<> cs)) (CsTupleTy anns' (map toTyTupArg ts))
    where
      toTyTupArg :: Either (EpAnn Bool) (LCsType Ps) -> CsTyTupArg Ps
      toTyTupArg (Left ann) = TyMissing ann 
      toTyTupArg (Right a) = TyPresent noExtField a
      anns' = case anns of
        [AddEpAnn AnnOpenP ol, AddEpAnn AnnCloseP cl] ->
          AnnParen AnnParens ol cl
        _ -> panic "mkSumOrTupleType bad anns"

mkSumOrTupleType l (Sum {}) _ = addFatalError $ mkPlainErrorMsgEnvelope (locA l) PsErrSumDCType

mkSumOrTuplePat
  :: SrcSpanAnnA
  -> SumOrTuple (PatBuilder Ps)
  -> [AddEpAnn]
  -> PV (LocatedA (PatBuilder Ps))
mkSumOrTuplePat l (Tuple ps) anns = do
  ps' <- traverse toTupPat ps
  return $ L l (PatBuilderPat (TuplePat anns ps'))
  where
    toTupPat :: Either (EpAnn Bool) (LocatedA (PatBuilder Ps)) -> PV (LPat Ps)
    toTupPat p = case p of
                   Left _ -> addFatalError $
                             mkPlainErrorMsgEnvelope (locA l) PsErrTupleSectionInPat
                   Right p' -> checkLPat p'
mkSumOrTuplePat l (Sum alt arity p barsb barsa) anns = do
  p' <- checkLPat p
  let an = EpAnnSumPat anns barsb barsa
  return $ L l (PatBuilderPat (SumPat an p' alt arity))

mkLCsOpTy :: LCsType Ps -> LocatedN RdrName -> LCsType Ps -> LCsType Ps
mkLCsOpTy x op y =
  let loc = locA x `combineSrcSpans` locA op `combineSrcSpans` locA y
  in L (noAnnSrcSpan loc) (mkCsOpTy x op y)

-----------------------------------------------------------------------------
-- Tuple punning

mkTupleSyntaxTycon :: Int -> P RdrName
mkTupleSyntaxTycon n = pure $ getRdrName (tupleTyCon n)
