{-# LANGUAGE DataKinds #-}

module CSlash.Tc.Types.Origin where

import Prelude hiding ((<>))

import CSlash.Tc.Utils.TcType

import CSlash.Cs

import CSlash.Core.TyCon

import CSlash.Types.Id
import CSlash.Types.Name
import CSlash.Types.Name.Reader
import CSlash.Types.Basic
import CSlash.Types.SrcLoc

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
  | GenSigCtxt
  | SigmaCtxt
  | TyVarBndrKindCtxt Name
  | TySynKindCtxt Name
  deriving (Eq)

data ReportRedundantConstraints
  = NoRRC
  | WantRRC SrcSpan
  deriving (Eq)

pprUserTypeCtxt :: UserTypeCtxt -> SDoc
pprUserTypeCtxt (FunSigCtxt n _) = text "the type signature for" <+> quotes (ppr n)
pprUserTypeCtxt (InfSigCtxt n) = text "the inferred type for" <+> quotes (ppr n)
pprUserTypeCtxt (ExprSigCtxt _) = text "an expression type signature"
pprUserTypeCtxt KindSigCtxt = text "a kind signature"
pprUserTypeCtxt TypeAppCtxt = text "a type argument"
pprUserTypeCtxt (ConArgCtxt c) = text "the type of the constructor" <+> quotes (ppr c)
pprUserTypeCtxt (TySynCtxt c) = text "the RHS of the type synonym" <+> quotes (ppr c)
pprUserTypeCtxt (PatSynCtxt _) = panic "currently unreachable"
pprUserTypeCtxt GenSigCtxt = text "a type expected by the context"
pprUserTypeCtxt SigmaCtxt = text "the context of a polymorphic type"
pprUserTypeCtxt (TyVarBndrKindCtxt n) = text "the kind annotation on the type variable"
                                        <+> quote (ppr n)
pprUserTypeCtxt (TySynKindCtxt n) = text "the kind annotation on the declaration for"
                                    <+> quotes (ppr n)

data SkolemInfo = SkolemInfo Unique SkolemInfoAnon

data SkolemInfoAnon
  = SigSkol UserTypeCtxt TcType [(Name, TcTyVar)]
  | SigTypeSkol UserTypeCtxt
  | ForAllSkol TyVarBndrs
  | TyLamTySkol [Name]
  | InferSkol [(Name, TcType)]
  | UnifyForAllSkol TcType
  | TyConSkol (TyConFlavor TyCon) Name
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
pprSkolInfo (SigTypeSkol cx) = pprUserTypeCtxt cx
pprSkolInfo (ForAllSkol tvs) = text "an explicit forall" <+> ppr tvs
pprSkolInfo (TyLamTySkol tvs) = text "an explicit type lambda" <+> ppr tvs
pprSkolInfo (InferSkol ids) = hang (text "the inferred type" <> plural ids <+> text "of")
                              2 (vcat [ ppr name <+> colon <+> ppr ty
                                      | (name, ty) <- ids ])
pprSkolInfo (UnifyForAllSkol ty) = text "the type" <+> ppr ty
pprSkolInfo (TyConSkol flav name) = text "the" <+> ppr flav
                                    <+> text "declaration for" <+> quotes (ppr name)
pprSkolInfo (UnkSkol cs) = text "UnkSkol (please report this as a bug)" $$ prettyCallStackDoc cs

pprSigSkolInfo :: UserTypeCtxt -> TcType -> SDoc
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

data KindedThing
  = CsTypeRnThing (CsType Rn)

data TyVarBndrs = CsTyVarBndrsRn [CsTyVarBndr Rn]

instance Outputable TyVarBndrs where
  ppr (CsTyVarBndrsRn bndrs) = fsep (map ppr bndrs)

data CtOrigin
  = OccurrenceOf Name
  | KindEqOrigin { keq_actual :: TcMonoKind
                 , keq_expected :: TcMonoKind
                 , keq_thing :: Maybe KindedThing
                 , keq_visible :: Bool
                 }

isVisibleOrigin :: CtOrigin -> Bool
isVisibleOrigin (KindEqOrigin { keq_visible = vis }) = vis
isVisibleOrigin _ = True

toInvisibleOrigin :: CtOrigin -> CtOrigin
toInvisibleOrigin o@(KindEqOrigin {}) = o { keq_visible = True }
toInvisibleOrigin o = o

isGivenOrigin :: CtOrigin -> Bool
isGivenOrigin (KindEqOrigin {}) = False
isGivenOrigin (OccurrenceOf {}) = False

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
pprCtOrigin (KindEqOrigin k1 k2 _ _)
  = hang (ctoHerald <+> text "a kind equality")
         2 (sep [ppr k1, char '~', ppr k2])

pprCtOrigin simple_origin = ctoHerald <+> pprCtO simple_origin

pprCtO :: HasCallStack => CtOrigin -> SDoc
pprCtO (OccurrenceOf name) = hsep [text "a use of", quotes (ppr name)]
pprCtO _ = panic "pprCtO"

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
