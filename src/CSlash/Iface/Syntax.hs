{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveTraversable #-}

module CSlash.Iface.Syntax
  ( module CSlash.Iface.Type
  , module CSlash.Iface.Syntax
  ) where

import Prelude hiding ((<>))

import CSlash.Data.FastString
-- import CSlash.Builtin.Names ( unrestrictedFunTyConKey, liftedTypeKindTyConKey,
--                               constraintKindTyConKey )
import CSlash.Types.Unique ( hasKey )
import CSlash.Iface.Type
import CSlash.Iface.Recomp.Binary
import CSlash.Core( {-IsOrphan, isOrphan,-} UnfoldingCache(..) )
import CSlash.Types.Demand
-- import GHC.Types.Cpr
-- import GHC.Core.Class
-- import GHC.Types.FieldLabel
import CSlash.Types.Name.Set
-- import GHC.Core.Coercion.Axiom ( BranchIndex )
import CSlash.Types.Name
-- import GHC.Types.CostCentre
import CSlash.Types.Literal
-- import GHC.Types.ForeignCall
-- import GHC.Types.Annotations( AnnPayload, AnnTarget )
import CSlash.Types.Basic
import CSlash.Unit.Module
import CSlash.Unit.Module.Warnings
import CSlash.Types.SrcLoc
import CSlash.Types.SourceText
-- import GHC.Data.BooleanFormula ( BooleanFormula(..), pprBooleanFormula, isTrue )
import CSlash.Types.Var( VarBndr(..), binderVar{-, tyVarSpecToBinders, visArgTypeLike-} )
-- import CSlash.Core.TyCon ( Role (..), Injectivity(..), tyConBndrVisForAllTyFlag )
-- import CSlash.Builtin.Types ( constraintKindTyConName )
-- import GHC.Stg.InferTags.TagSig
import CSlash.Parser.Annotation (noLocA)
import CSlash.Cs.Extension ( Rn )
import CSlash.Cs.Doc ( WithCsDocIdentifiers(..) )

import CSlash.Utils.Lexeme (isLexSym)
import CSlash.Utils.Fingerprint
import CSlash.Utils.Binary
-- import GHC.Utils.Binary.Typeable ()
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc( dropList, filterByList, notNull, unzipWith,
                          seqList, zipWithEqual )

import Control.Monad
import System.IO.Unsafe
import Control.DeepSeq

{- *********************************************************************
*                                                                      *
                    Declarations
*                                                                      *
********************************************************************* -}

type IfaceTopBndr = Name

data IfaceDecl
  = IfaceId
    { ifName :: IfaceTopBndr
    , ifType :: IfaceType
    , ifIdDetails :: IfaceIdDetails
    , ifIdInfo :: IfaceIdInfo
    }
  | IfaceData
    { ifName :: IfaceTopBndr
    , ifBinders :: [IfaceTyConBinder]
    , ifResKind :: IfaceKind
    , ifCons :: IfaceConDecls
    }
  | IfaceSynonym
    { ifName :: IfaceTopBndr
    , ifBinders :: [IfaceTyConBinder]
    , ifResKind :: IfaceKind
    , ifSynRhs :: IfaceType
    }

data IfaceConDecls
  = IfAbstractTyCon
  | IfDataTyCon [IfaceConDecl]

data IfaceConDecl
  = IfCon
    { ifConName :: IfaceTopBndr
    , ifConInfix :: Bool
    , ifConTvBinders :: [IfaceBndr]
    , ifConArgTys :: [IfaceType]
    }

data IfaceWarnings
  = IfWarnAll IfaceWarningTxt
  | IfWarnSome [(OccName, IfaceWarningTxt)] [(IfExtName, IfaceWarningTxt)]

data IfaceWarningTxt
  = IfWarningTxt (Maybe WarningCategory) SourceText [(IfaceStringLiteral, [IfExtName])]
  | IfDeprecatedTxt SourceText [(IfaceStringLiteral, [IfExtName])]

data IfaceStringLiteral = IfStringLiteral SourceText FastString

data IfaceAnnotation

data IfaceCompleteMatch

instance Outputable IfaceCompleteMatch

type IfaceIdInfo = [IfaceInfoItem]

data IfaceInfoItem
  = CsArity Arity
  | CsDmdSig DmdSig
  | CsInline InlinePragma
  | CsUnfold Bool IfaceUnfolding
  | CsNoCafRefs
  | CsLFInfo IfaceLFInfo

data IfaceUnfolding
  = IfCoreUnfold UnfoldingSource
                 IfUnfoldingCache
                 IfGuidance
                 IfaceExpr

type IfUnfoldingCache = UnfoldingCache

data IfGuidance
  = IfNoGuidance
  | IfWhen Arity Bool Bool

data IfaceIdDetails
  = IfVanillaId

data IfaceLFInfo
  = IfLFReEntrant !Arity
  | IfLFCon !Name
  | IfLFUnknown !Bool

instance Outputable IfaceLFInfo where
  ppr (IfLFReEntrant arity) = text "LFReEntrant" <+> ppr arity
  ppr (IfLFCon con) = text "LFCon" <> brackets (ppr con)
  ppr (IfLFUnknown fun_flag) = text "LFUnknown" <+> ppr fun_flag

instance Binary IfaceLFInfo where
    put_ bh (IfLFReEntrant arity) = do
        putByte bh 0
        put_ bh arity
    put_ bh (IfLFCon con_name) = do
        putByte bh 2
        put_ bh con_name
    put_ bh (IfLFUnknown fun_flag) = do
        putByte bh 3
        put_ bh fun_flag
    get bh = do
        tag <- getByte bh
        case tag of
            0 -> IfLFReEntrant <$> get bh
            2 -> IfLFCon <$> get bh
            3 -> IfLFUnknown <$> get bh
            _ -> panic "Invalid byte"


{- *********************************************************************
*                                                                      *
                Functions over declarations
*                                                                      *
********************************************************************* -}

ifaceDeclImplicitBndrs :: IfaceDecl -> [OccName]
ifaceDeclImplicitBndrs (IfaceData { ifName = tc_name, ifCons = cons })
  = case cons of
      IfAbstractTyCon -> []
      IfDataTyCon cds -> concatMap ifaceConDeclImplicitBndrs cds
ifaceDeclImplicitBndrs _ = []

ifaceConDeclImplicitBndrs :: IfaceConDecl -> [OccName]
ifaceConDeclImplicitBndrs (IfCon { ifConName = con_name })
  = [occName con_name, mkDataConOcc (occName con_name)]

-- -----------------------------------------------------------------------------
-- The fingerprints of an IfaceDecl

ifaceDeclFingerprints :: Fingerprint -> IfaceDecl -> [(OccName, Fingerprint)]
ifaceDeclFingerprints hash decl
  = (getOccName decl, hash) :
  [ (occ, computeFingerprint' (hash, occ))
  | occ <- ifaceDeclImplicitBndrs decl ]
  where
    computeFingerprint' =
      unsafeDupablePerformIO . computeFingerprint (panic "ifaceDeclFingerprints")

fromIfaceWarnings :: IfaceWarnings -> Warnings Rn
fromIfaceWarnings = \case
  IfWarnAll txt -> WarnAll (fromIfaceWarningTxt txt)
  IfWarnSome vs ds -> WarnSome [(occ, fromIfaceWarningTxt txt) | (occ, txt) <- vs]
                               [(occ, fromIfaceWarningTxt txt) | (occ, txt) <- ds]

fromIfaceWarningTxt :: IfaceWarningTxt -> WarningTxt Rn
fromIfaceWarningTxt = \case
  IfWarningTxt mb_cat src strs -> WarningTxt
    (noLocA . fromWarningCategory <$> mb_cat)
    src
    (noLocA <$> map fromIfaceStringLiteralWithNames strs)
  IfDeprecatedTxt src strs -> DeprecatedTxt
    src
    (noLocA <$> map fromIfaceStringLiteralWithNames strs)

fromIfaceStringLiteralWithNames
  :: (IfaceStringLiteral, [IfExtName]) -> WithCsDocIdentifiers StringLiteral Rn
fromIfaceStringLiteralWithNames (str, names)
  = WithCsDocIdentifiers (fromIfaceStringLiteral str) (map noLoc names)

fromIfaceStringLiteral :: IfaceStringLiteral -> StringLiteral
fromIfaceStringLiteral (IfStringLiteral st fs) = StringLiteral st fs Nothing

{- *********************************************************************
*                                                                      *
                Expressions
*                                                                      *
********************************************************************* -}

data IfaceExpr

data IfaceBinding b = IfaceBindingX IfaceExpr b

data IfaceBindingX r b
  = IfaceNonRec b r
  | IfaceRec [(b, r)]
  deriving (Functor, Foldable, Traversable, Ord, Eq)

data IfaceTopBndrInfo
  = IfLclTopBndr IfLclName IfaceType IfaceIdInfo IfaceIdDetails
  | IfGblTopBndr IfaceTopBndr

data IfaceMaybeRhs = IfUseUnfoldingRhs | IfRhs IfaceExpr

{- *********************************************************************
*                                                                      *
              Printing IfaceDecl
*                                                                      *
********************************************************************* -}

instance NamedThing IfaceConDecl where
  getName = ifConName

instance HasOccName IfaceConDecl where
  occName = getOccName

instance NamedThing IfaceDecl where
  getName = ifName

instance HasOccName IfaceDecl where
  occName = getOccName

instance Outputable IfaceDecl where
  ppr = pprIfaceDecl showToIface

instance (Outputable r, Outputable b) => Outputable (IfaceBindingX r b)

instance Outputable IfaceTopBndrInfo

instance Outputable IfaceMaybeRhs

showToIface :: ShowSub
showToIface = ShowSub ShowIface

pprIfaceDecl :: ShowSub -> IfaceDecl -> SDoc
pprIfaceDecl = undefined  

{- *********************************************************************
*                                                                      *
                Binary instances
*                                                                      *
********************************************************************* -}

instance Binary IfaceDecl

instance Binary IfaceAnnotation

instance (Binary r, Binary b) => Binary (IfaceBindingX b r)

instance Binary IfaceTopBndrInfo

instance Binary IfaceMaybeRhs

instance Binary IfaceCompleteMatch
