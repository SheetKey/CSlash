{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
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
  | isRdrTc name = return $ emptyComments Semi.<> comments l
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
    check err a = addError $ mkPlainErrorMsgEnvelope (getLocA a) $ (err a)
      
-- -------------------------------------------------------------------------
-- Checking Patterns.

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
  | isRdrDataCon c = return ( L loc $ ConPat
                              { pat_con_ext = noAnn
                              , pat_con = L ln c
                              , pat_args = PrefixCon tyargs args
                              }
                            , comments l Semi.<> cs)
checkPat loc cs (L la (PatBuilderAppType f t)) tyargs args =
  checkPat loc (cs Semi.<> comments la) f (CsConPatTyArg noExtField t : tyargs) args
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
checkAPat loc e0 = do
  case e0 of
    PatBuilderPat p -> return p
    PatBuilderVar x -> return (VarPat noExtField x)
    PatBuilderOverLit pos_lit -> return (mkNPat (L (l2l loc) pos_lit) Nothing noAnn)
    PatBuilderOpApp _ op _ _
      | opIsAt (unLoc op) -> do
          addError $ mkPlainErrorMsgEnvelope (getLocA op) PsErrAtInPatPos
          return (WildPat noExtField)
    PatBuilderOpApp l (L cl c) r anns
      | isRdrDataCon c -> do
          l <- checkLPat l
          r <- checkLPat r
          return $ ConPat
            { pat_con_ext = anns
            , pat_con = L cl c
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

-- -------------------------------------------------------------------------
-- Expression/command/pattern ambiguity.

newtype ECP
  = ECP { unECP :: forall b. DisambECP b => PV (LocatedA b) }

ecpFromExp :: LCsExpr Ps -> ECP
ecpFromExp a = ECP (ecpFromExp' a)

-- Currently NOT setting the namespace
class DisambInfixOp b where
  mkCsVarOpPV :: LocatedN RdrName -> PV (LocatedN b)
  mkCsConOpPV :: LocatedN RdrName -> PV (LocatedN b)

instance DisambInfixOp (CsExpr Ps) where
  mkCsVarOpPV (L l rn) = assert (isRdrUnknown rn) $
                         return $ L l (CsVar noExtField (L l rn))
  mkCsConOpPV (L l rn) = assert (isRdrUnknown rn) $
                         return $ L l (CsVar noExtField (L l rn))

instance DisambInfixOp RdrName where
  mkCsVarOpPV (L l v) = assert (isRdrUnknown v) $
                        return $ L l v
  mkCsConOpPV (L l v) = assert (isRdrUnknown v) $
                        return $ L l v

type AnnoBody b
  = ( Anno (GRHS Ps (LocatedA (Body b Ps))) ~ EpAnnCO
    , Anno [LocatedA (Match Ps (LocatedA (Body b Ps)))] ~ SrcSpanAnnL
    , Anno (Match Ps (LocatedA (Body b Ps))) ~ SrcSpanAnnA
    , Anno (StmtLR Ps Ps (LocatedA (Body (Body b Ps) Ps))) ~ SrcSpanAnnA
    , Anno [LocatedA (StmtLR Ps Ps
                      (LocatedA (Body (Body (Body b Ps) Ps) Ps)))] ~ SrcSpanAnnL
    )

class (b ~ (Body b) Ps, AnnoBody b) => DisambECP b where
  type Body b :: K.Type -> K.Type
  ecpFromExp' :: LCsExpr Ps -> PV (LocatedA b)
  mkCsLetPV
    :: SrcSpan
    -> EpToken "let"
    -> CsLocalBinds Ps
    -> EpToken "in"
    -> LocatedA b
    -> PV (LocatedA b)
  type InfixOp b
  superInfixOp :: (DisambInfixOp (InfixOp b) => PV (LocatedA b)) -> PV (LocatedA b)
  mkCsOpAppPV
    :: SrcSpan
    -> LocatedA b
    -> LocatedN (InfixOp b)
    -> LocatedA b
    -> PV (LocatedA b)
  mkCsCasePV
    :: SrcSpan
    -> LCsExpr Ps
    -> (LocatedL [LMatch Ps (LocatedA b)])
    -> EpAnnCsCase
    -> PV (LocatedA b)
  mkCsLamPV
    :: SrcSpan
    -> (LocatedL [LMatch Ps (LocatedA b)])
    -> [AddEpAnn]
    -> PV (LocatedA b)
  type FunArg b
  superFunArg :: (DisambECP (FunArg b) => PV (LocatedA b)) -> PV (LocatedA b)
  mkCsAppPV
    :: SrcSpanAnnA
    -> LocatedA b
    -> LocatedA (FunArg b)
    -> PV (LocatedA b)
  mkCsAppTypePV
    :: SrcSpanAnnA
    -> LocatedA b
    -> LCsType Ps
    -> PV (LocatedA b)
  mkCsIfPV
    :: SrcSpan
    -> LCsExpr Ps
    -> LocatedA b
    -> LocatedA b
    -> AnnsIf
    -> PV (LocatedA b)
  mkCsParPV :: SrcSpan -> EpToken "(" -> LocatedA b -> EpToken ")" -> PV (LocatedA b)
  mkCsVarPV :: LocatedN RdrName -> PV (LocatedA b)
  mkCsLitPV :: Located (CsLit Ps) -> PV (LocatedA b)
  mkCsOverLitPV :: LocatedAn a (CsOverLit Ps) -> PV (LocatedAn a b)
  mkCsWildCardPV :: (NoAnn a) => SrcSpan -> PV (LocatedAn a b)
  mkCsTySigPV :: SrcSpanAnnA -> LocatedA b -> LCsType Ps -> [AddEpAnn] -> PV (LocatedA b)
  mkCsNegAppPV :: SrcSpan -> LocatedA b -> [AddEpAnn] -> PV (LocatedA b)
  mkCsSectionR_PV :: SrcSpan -> LocatedA (InfixOp b) -> LocatedA b -> PV (LocatedA b)
  mkCsAsPatPV :: SrcSpan -> LocatedN RdrName -> EpToken "@" -> LocatedA b -> PV (LocatedA b)
  mkSumOrTuplePV :: SrcSpanAnnA -> SumOrTuple b -> [AddEpAnn] -> PV (LocatedA b)

checkLamMatchGroup :: SrcSpan -> MatchGroup Ps (LCsExpr Ps) -> PV ()
checkLamMatchGroup l (MG { mg_alts = (L _ (matches:_)) }) = do
  when (null (csLMatchPats matches)) $ addError $ mkPlainErrorMsgEnvelope l PsErrEmptyLambda

instance DisambECP (CsExpr Ps) where
  type Body (CsExpr Ps) = CsExpr
  ecpFromExp' = return
  mkCsLetPV l tkLet bs tkIn c = do
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsLet (tkLet, tkIn) bs c)
  type InfixOp (CsExpr Ps) = CsExpr Ps
  superInfixOp m = m
  mkCsOpAppPV l e1 op e2 = do
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) $ OpApp [] e1 (reLoc op) e2
  mkCsCasePV l e (L lm m) anns = do
    !cs <- getCommentsFor l
    let mg = mkMatchGroup FromSource (L lm m)
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsCase anns e mg)
  mkCsLamPV l (L lm m) anns = do
    !cs <- getCommentsFor l
    let mg = mkLamMatchGroup FromSource (L lm m)
    checkLamMatchGroup l mg
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsLam anns mg)
  type FunArg (CsExpr Ps) = CsExpr Ps
  superFunArg m = m
  mkCsAppPV l e1 e2 = do
    checkExpBlockArguments e1
    checkExpBlockArguments e2
    return $ L l (CsApp noExtField e1 e2)
  mkCsAppTypePV l e t = do
    checkExpBlockArguments e
    return $ L l (CsTyApp noExtField e (L (l2l t) $ CsEmbTy noExtField t))
  mkCsIfPV l c a b anns = do
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (mkCsIf c a b anns)
  mkCsParPV l lpar e rpar = do
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsPar (lpar, rpar) e)
  mkCsVarPV v@(L l@(EpAnn anc _ _) _) = do
    !cs <- getCommentsFor (getHasLoc l)
    return $ L (EpAnn anc noAnn cs) (CsVar noExtField v)
  mkCsLitPV (L l a) = do
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (CsLit noExtField a)
  mkCsOverLitPV (L (EpAnn l an csIn) a) = do
    !cs <- getCommentsFor (locA l)
    return $ L (EpAnn l an (cs Semi.<> csIn)) (CsOverLit noExtField a)
  mkCsWildCardPV l = return $ L (noAnnSrcSpan l) (csHoleExpr noAnn)
  mkCsTySigPV l@(EpAnn anc an csIn) a sig anns = do
    !cs <- getCommentsFor (locA l)
    return $ L (EpAnn anc an (csIn Semi.<> cs)) (ExprWithTySig anns a (csTypeToCsSigType sig))
  mkCsNegAppPV l a anns = do
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (NegApp anns a noSyntaxExpr)
  mkCsSectionR_PV l op e = do
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (SectionR noExtField op e)
  mkCsAsPatPV l v _ e = addError (mkPlainErrorMsgEnvelope l PsErrUnexpectedAsPat)
                        >> return (L (noAnnSrcSpan l) (csHoleExpr noAnn))
  mkSumOrTuplePV = mkSumOrTupleExpr

csHoleExpr :: Maybe EpAnnUnboundVar -> CsExpr Ps
csHoleExpr anns = CsUnboundVar anns (mkRdrUnqual (mkVarOccFS (fsLit "_")))

instance DisambECP (PatBuilder Ps) where
  type Body (PatBuilder Ps) = PatBuilder
  ecpFromExp' (L l e) = addFatalError $ mkPlainErrorMsgEnvelope (locA l) $ PsErrArrowExprInPat e
  mkCsLetPV l _ _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrLetInPat
  type InfixOp (PatBuilder Ps) = RdrName
  superInfixOp m = m
  mkCsOpAppPV l p1 op p2 = do
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) $ PatBuilderOpApp p1 op p2 []
  mkCsLamPV l _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrLambdaInPat
  mkCsCasePV l _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrCaseInPat
  type FunArg (PatBuilder Ps) = PatBuilder Ps
  superFunArg m = m
  mkCsAppPV l p1 p2 = return $ L l (PatBuilderApp p1 p2)
  mkCsAppTypePV l p t = do
    !cs <- getCommentsFor (locA l)
    return $ L (addCommentsToEpAnn l cs) (PatBuilderAppType p (mkCsTyPat t))
  mkCsIfPV l _ _ _ _ = addFatalError $ mkPlainErrorMsgEnvelope l PsErrIfInPat
  mkCsParPV l lpar p rpar = return $ L (noAnnSrcSpan l) (PatBuilderPar lpar p rpar)
  mkCsVarPV v@(getLoc -> l) = return $ L (l2l l) (PatBuilderVar v)
  mkCsLitPV lit@(L l a) = do
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (PatBuilderPat (LitPat noExtField a))
  mkCsOverLitPV (L l a) = return $ L l (PatBuilderOverLit a)
  mkCsWildCardPV l = return $ L (noAnnSrcSpan l) (PatBuilderPat (WildPat noExtField))
  mkCsTySigPV l b sig anns = do
    p <- checkLPat b
    return $ L l (PatBuilderPat (SigPat anns p (mkCsPatSigType noAnn sig)))
  mkCsNegAppPV l (L lp p) anns = do
    lit <- case p of
             PatBuilderOverLit pos_lit -> return (L (l2l lp) pos_lit)
             _ -> patFail l $ PsErrInPat p PEIP_NegApp
    !cs <- getCommentsFor l
    return
      $ L (EpAnn (spanAsAnchor l) noAnn cs) (PatBuilderPat (mkNPat lit (Just noSyntaxExpr) anns))
  mkCsSectionR_PV l op p = patFail l (PsErrParseRightOpSectionInPat (unLoc op) (unLoc p))
  mkCsAsPatPV l v at e = do
    p <- checkLPat e
    !cs <- getCommentsFor l
    return $ L (EpAnn (spanAsAnchor l) noAnn cs) (PatBuilderPat (AsPat at v p))
  mkSumOrTuplePV = mkSumOrTuplePat

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
        -> return $ IETyVar noExtField (L l (ieNameFromSpec specname))
      | otherwise -> panic "mkModuleImpExp"
  where
    ieNameFromSpec :: ImpExpQcSpec -> IEWrappedName Ps
    ieNameFromSpec (ImpExpQcName (L l n)) = IEName noExtField (L l n)
    ieNameFromSpec (ImpExpQcTyVar r (L l n)) = IETyVar r (L l n)

-- forward compatability:
-- checks that imports of the form 'Thing(Thing1, Thing2, ..)'
-- are handled properly
checkImportSpec :: LocatedL [LIE Ps] -> P (LocatedL [LIE Ps])
checkImportSpec = pure


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
