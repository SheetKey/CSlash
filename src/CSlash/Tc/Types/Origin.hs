{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module CSlash.Tc.Types.Origin where

import Prelude hiding ((<>))

import CSlash.Tc.Utils.TcType

import CSlash.Cs

import CSlash.Core.TyCon
import CSlash.Core.Type
import CSlash.Core.Kind

import CSlash.Types.Var.Id
import CSlash.Types.Name
import CSlash.Types.Name.Reader
import CSlash.Types.Basic
import CSlash.Types.SrcLoc
import CSlash.Types.Var (TyVar, TcTyVar, KiVar, TcKiVar)

import CSlash.Data.FastString

import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Types.Unique
import CSlash.Types.Unique.Supply

import GHC.Exception
import GHC.Stack (callStack)

import CSlash.Utils.Misc
import Control.Monad.IO.Class ( MonadIO(..) )

data UserTypeCtxt
  = FunSigCtxt Name ReportRedundantConstraints
  | InfSigCtxt Name
  | ExprSigCtxt ReportRedundantConstraints
  | KindSigCtxt
  | TypeAppCtxt
  | ConArgCtxt Name
  | TySynCtxt Name
  | PatSynCtxt Name
  | PatSigCtxt
  | GenSigCtxt
  | SigmaCtxt
  | TyVarBndrKindCtxt Name
  | TySynKindCtxt Name
  deriving (Eq)

data ReportRedundantConstraints
  = NoRRC
  | WantRRC SrcSpan
  deriving (Eq)

reportRedundantConstraints :: ReportRedundantConstraints -> Bool
reportRedundantConstraints NoRRC = False
reportRedundantConstraints (WantRRC {}) = True

pprUserTypeCtxt :: UserTypeCtxt -> SDoc
pprUserTypeCtxt (FunSigCtxt n _) = text "the type signature for" <+> quotes (ppr n)
pprUserTypeCtxt (InfSigCtxt n) = text "the inferred type for" <+> quotes (ppr n)
pprUserTypeCtxt (ExprSigCtxt _) = text "an expression type signature"
pprUserTypeCtxt KindSigCtxt = text "a kind signature"
pprUserTypeCtxt TypeAppCtxt = text "a type argument"
pprUserTypeCtxt (ConArgCtxt c) = text "the type of the constructor" <+> quotes (ppr c)
pprUserTypeCtxt (TySynCtxt c) = text "the RHS of the type synonym" <+> quotes (ppr c)
pprUserTypeCtxt PatSigCtxt = text "a pattern type signature"
pprUserTypeCtxt (PatSynCtxt _) = panic "currently unreachable"
pprUserTypeCtxt GenSigCtxt = text "a type expected by the context"
pprUserTypeCtxt SigmaCtxt = text "the context of a polymorphic type"
pprUserTypeCtxt (TyVarBndrKindCtxt n) = text "the kind annotation on the type variable"
                                        <+> quote (ppr n)
pprUserTypeCtxt (TySynKindCtxt n) = text "the kind annotation on the declaration for"
                                    <+> quotes (ppr n)

isSigMaybe :: UserTypeCtxt -> Maybe Name
isSigMaybe (FunSigCtxt n _) = Just n
isSigMaybe (ConArgCtxt n) = Just n
isSigMaybe (PatSynCtxt n) = Just n
isSigMaybe _ = Nothing

{- *********************************************************************
*                                                                      *
                SkolemInfo
*                                                                      *
********************************************************************* -}

data SkolemInfo = SkolemInfo Unique SkolemInfoAnon

data SkolemInfoAnon
  = SigSkol UserTypeCtxt (Type Tc) [(Name, TcTyVar)]
  | SigSkolKi UserTypeCtxt (Type Tc) [(Name, TcKiVar)]
  | SigTypeSkol UserTypeCtxt
  | ForAllSkol TyVarBndrs
  | TyLamTySkol [Name]
  | InferSkol [(Name, Type Tc)]
  | InferKindSkol
  | UnifyForAllSkol (Type Tc)
  | TyConSkol TyConFlavor Name
  | UnkSkol CallStack

unkSkol :: HasDebugCallStack => SkolemInfo
unkSkol = SkolemInfo (mkUniqueGrimily 0) unkSkolAnon

unkSkolAnon :: HasDebugCallStack => SkolemInfoAnon
unkSkolAnon = UnkSkol callStack

mkSkolemInfo :: MonadIO m => SkolemInfoAnon -> m SkolemInfo
mkSkolemInfo sk_anon = do
  u <- liftIO $! uniqFromTag 's'
  return (SkolemInfo u sk_anon)

getSkolemInfo :: SkolemInfo -> SkolemInfoAnon
getSkolemInfo (SkolemInfo _ skol_anon) = skol_anon

instance Outputable SkolemInfo where
  ppr (SkolemInfo _ sk_info) = ppr sk_info

instance Outputable SkolemInfoAnon where
  ppr = pprSkolInfo

pprSkolInfo :: SkolemInfoAnon -> SDoc
pprSkolInfo (SigSkol cx ty _) = pprSigSkolInfo cx ty
pprSkolInfo (SigSkolKi cx ty _) = pprSigSkolInfo cx ty
pprSkolInfo (SigTypeSkol cx) = pprUserTypeCtxt cx
pprSkolInfo (ForAllSkol tvs) = text "an explicit forall" <+> ppr tvs
pprSkolInfo (TyLamTySkol tvs) = text "an explicit type lambda" <+> ppr tvs
pprSkolInfo (InferSkol ids) = hang (text "the inferred type" <> plural ids <+> text "of")
                              2 (vcat [ ppr name <+> colon <+> ppr ty
                                      | (name, ty) <- ids ])
pprSkolInfo InferKindSkol = text "the inferred kind"
pprSkolInfo (UnifyForAllSkol ty) = text "the type" <+> ppr ty
pprSkolInfo (TyConSkol flav name) = text "the" <+> ppr flav
                                    <+> text "declaration for" <+> quotes (ppr name)
pprSkolInfo (UnkSkol cs) = text "UnkSkol (please report this as a bug)" $$ prettyCallStackDoc cs

pprSigSkolInfo :: UserTypeCtxt -> Type Tc -> SDoc
pprSigSkolInfo ctxt ty = case ctxt of
  FunSigCtxt f _ -> vcat [ text "the type signature for:"
                         , nest 2 (pprPrefixOcc f <+> colon <+> ppr ty) ]
  PatSynCtxt {} -> panic "currently unreachable"
  _ -> vcat [ pprUserTypeCtxt ctxt <> colon, nest 2 (ppr ty) ]

{- *********************************************************************
*                                                                      *
            CtOrigin
*                                                                      *
********************************************************************* -}

data TypedThing
  = NameThing Name
  | CsExprRnThing (CsExpr Rn)
  | CsExprTcThing (CsExpr Tc)

instance Outputable TypedThing where
  ppr (NameThing name) = ppr name
  ppr (CsExprRnThing expr) = ppr expr
  ppr (CsExprTcThing expr) = ppr expr

data KindedThing
  = CsTypeRnThing (CsType Rn)
  | KiNameThing Name
  | TypeThing (Type Tc)

data TyVarBndrs = CsTyVarBndrsRn [CsTyVarBndr Rn]

instance Outputable TyVarBndrs where
  ppr (CsTyVarBndrsRn bndrs) = fsep (map ppr bndrs)

data CtOrigin -- DOUBLE CHECK PATTERN MATCHES IF YOU ADD 'AmbiguityCheckOrigin' OR 'CycleBreakerOrigin'
  = GivenOrigin SkolemInfoAnon
  | OccurrenceOf Name
  | TypeEqOrigin { uo_actual :: Type Tc
                 , uo_expected :: Type Tc
                 , uo_thing :: Maybe TypedThing
                 , uo_visible :: Bool
                 }
  | KindEqOrigin (Type Tc) (Type Tc) CtOrigin
  | KindCoOrigin { kco_actual :: MonoKind Tc
                 , kco_expected :: MonoKind Tc
                 , kco_pred :: KiPredCon
                 , kco_thing :: Maybe KindedThing
                 , kco_visible :: Bool
                 }
  | LiteralOrigin (CsOverLit Rn)
  | SectionOrigin
  | ExprSigOrigin
  | TupleTyOrigin
  | PatSigOrigin
  | PatOrigin
  | UsageEnvironmentOf Name
  | IfThenElseOrigin
  | ImpedanceMatching (Id Tc)
  | Shouldn'tHappenOrigin String

isVisibleOrigin :: CtOrigin -> Bool
isVisibleOrigin (KindCoOrigin { kco_visible = vis }) = vis
isVisibleOrigin (TypeEqOrigin { uo_visible = vis }) = vis
isVisibleOrigin (KindEqOrigin _ _ sub_orig) = isVisibleOrigin sub_orig
isVisibleOrigin _ = True

toInvisibleOrigin :: CtOrigin -> CtOrigin
toInvisibleOrigin o@(KindCoOrigin {}) = o { kco_visible = True }
toInvisibleOrigin o@(TypeEqOrigin {}) = o { uo_visible = True }
toInvisibleOrigin o = o

isGivenOrigin :: CtOrigin -> Bool
isGivenOrigin (GivenOrigin {}) = True
isGivenOrigin _ = False

lexprCtOrigin :: LCsExpr Rn -> CtOrigin
lexprCtOrigin (L _ e) = exprCtOrigin e

exprCtOrigin :: CsExpr Rn -> CtOrigin
exprCtOrigin (CsVar _ (L _ name)) = OccurrenceOf name
exprCtOrigin (CsUnboundVar {}) = Shouldn'tHappenOrigin "unbound variable"
exprCtOrigin (CsOverLit _ lit) = LiteralOrigin lit
exprCtOrigin (CsLit {}) = Shouldn'tHappenOrigin "concrete literal"
exprCtOrigin (CsLam _ ms) = matchesCtOrigin ms
exprCtOrigin (CsTyLam _ ms) = matchesCtOrigin ms
exprCtOrigin (CsApp _ e1 _) = lexprCtOrigin e1
exprCtOrigin (OpApp _ _ op _) = lexprCtOrigin op
exprCtOrigin (NegApp _ e _) = lexprCtOrigin e
exprCtOrigin (CsPar _ e) = lexprCtOrigin e
exprCtOrigin (SectionL _ _ _) = SectionOrigin
exprCtOrigin (SectionR _ _ _) = SectionOrigin
exprCtOrigin (ExplicitTuple {}) = Shouldn'tHappenOrigin "explicit tuple"
exprCtOrigin (ExplicitSum {}) = Shouldn'tHappenOrigin "explicit sum"
exprCtOrigin (CsCase _ _ matches) = matchesCtOrigin matches
exprCtOrigin (CsIf {}) = IfThenElseOrigin
exprCtOrigin (CsMultiIf _ rhs) = lGRHSCtOrigin rhs
exprCtOrigin (CsLet _ _ e) = lexprCtOrigin e
exprCtOrigin (ExprWithTySig {}) = ExprSigOrigin
exprCtOrigin (CsEmbTy {}) = Shouldn'tHappenOrigin "type expression"
exprCtOrigin (XExpr x) = dataConCantHappen x

matchesCtOrigin :: MatchGroup Rn (LCsExpr Rn) -> CtOrigin
matchesCtOrigin (MG { mg_alts = alts })
  | L _ [L _ match] <- alts
  , Match { m_grhss = grhss } <- match
  = grhssCtOrigin grhss
  | otherwise
  = Shouldn'tHappenOrigin "multi-way match"

grhssCtOrigin :: GRHSs Rn (LCsExpr Rn) -> CtOrigin
grhssCtOrigin (GRHSs { grhssGRHSs = lgrhss }) = lGRHSCtOrigin lgrhss

lGRHSCtOrigin :: [LGRHS Rn (LCsExpr Rn)] -> CtOrigin
lGRHSCtOrigin [L _ (GRHS _ _ (L _ e))] = exprCtOrigin e
lGRHSCtOrigin _ = Shouldn'tHappenOrigin "multi-way GRHS"

instance Outputable CtOrigin where
  ppr = pprCtOrigin

ctoHerald :: SDoc
ctoHerald = text "arising from"

lCsTyCtOrigin :: LCsType Rn -> CtOrigin
lCsTyCtOrigin = csTyCtOrigin . unLoc

csTyCtOrigin :: CsType Rn -> CtOrigin
csTyCtOrigin (CsTyVar _ (L _ name)) = OccurrenceOf name
csTyCtOrigin _ = panic "lCsTypeCtOrigin"

pprCtOrigin :: CtOrigin -> SDoc

pprCtOrigin (GivenOrigin sk) = ctoHerald <+> ppr sk

pprCtOrigin (TypeEqOrigin t1 t2 _ vis)
  = hang (ctoHerald <+> text "a type equality" <> whenPprDebug (brackets (ppr vis)))
    2 (sep [ppr t1, char '~', ppr t2])

pprCtOrigin (KindCoOrigin k1 k2 kc _ _)
  = hang (ctoHerald <+> text "a kind coercion")
         2 (sep [ppr k1, char '`' <> ppr kc <> char '`', ppr k2])

pprCtOrigin (KindEqOrigin t1 t2 _)
  = hang (ctoHerald <+> text "a kind equality arising from")
    2 (sep [ppr t1, char '~', ppr t2])

pprCtOrigin (Shouldn'tHappenOrigin note)
  = vcat [ text "<< This should not appear in error messages. If you see this"
         , text "in an error message, it is a bug relating to"
           <+> quotes (text note) ]

pprCtOrigin simple_origin = ctoHerald <+> pprCtO simple_origin

pprCtO :: HasCallStack => CtOrigin -> SDoc
pprCtO (OccurrenceOf name) = hsep [text "a use of", quotes (ppr name)]

pprCtO TupleTyOrigin = text "a tuple type"
pprCtO PatSigOrigin = text "a pattern type signature"
pprCtO (UsageEnvironmentOf x) = hsep [ text "usage of", quotes (ppr x) ]

pprCtO (GivenOrigin {}) = text "a given constraint"
pprCtO _ = panic "pprCtO"

{- *******************************************************************
*                                                                    *
                       ExpectedFunTy origin
*                                                                    *
******************************************************************* -}

data ExpectedFunTyOrigin
  = forall (p :: Pass). Outputable (CsExpr (CsPass p))
    => ExpectedFunTyArg !TypedThing !(CsExpr (CsPass p))
  | ExpectedFunTyLam !(CsExpr Rn)

pprExpectedFunTyHerald :: ExpectedFunTyOrigin -> SDoc
pprExpectedFunTyHerald (ExpectedFunTyArg fun _)
  = sep [ text "The function" <+> quotes (ppr fun)
        , text "is applied to" ]
pprExpectedFunTyHerald (ExpectedFunTyLam expr)
  = sep [ text "The lambda expression" <+> quotes (pprSetDepth (PartWay 1) (ppr expr))
        , text "has" ]

{- *******************************************************************
*                                                                    *
                       InstanceWhat
*                                                                    *
******************************************************************* -}

data InstanceWhat
  = BuiltinEqInstance
  | BuiltinInstance
  | LocalInstance

instance Outputable InstanceWhat where
  ppr BuiltinEqInstance = text "a built-in equality instance"
  ppr BuiltinInstance = text "a built-in instance"
  ppr LocalInstance = text "a locally-quantified instance"
