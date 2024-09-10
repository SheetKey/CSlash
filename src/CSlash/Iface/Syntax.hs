{-# LANGUAGE DeriveTraversable #-}

module CSlash.Iface.Syntax
  ( module CSlash.Iface.Type
  , module CSlash.Iface.Syntax
  ) where

import CSlash.Data.FastString
-- import CSlash.Builtin.Names ( unrestrictedFunTyConKey, liftedTypeKindTyConKey,
--                               constraintKindTyConKey )
import CSlash.Types.Unique ( hasKey )
import CSlash.Iface.Type
-- import GHC.Iface.Recomp.Binary
-- import CSlash.Core( IsOrphan, isOrphan, UnfoldingCache(..) )
-- import GHC.Types.Demand
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
-- import GHC.Hs.Doc ( WithHsDocIdentifiers(..) )

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

type IfaceToppBndr = Name

data IfaceDecl
  -- = IfaceId
  --   { ifName :: IfaceTopBndr
  --   , ifType :: IfaceType
  --   , ifIdDetails :: IfaceIdDetails
  --   , ifIdInfo :: IfaceIdInfo
  --   }

data IfaceAnnotation

data IfaceCompleteMatch

type IfaceIdInfo = [IfaceInfoItem]

data IfaceInfoItem

data IfaceIdDetails

{- *********************************************************************
*                                                                      *
                Functions over declarations
*                                                                      *
********************************************************************* -}

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
  | IfGblTopBndr IfaceToppBndr

data IfaceMaybeRhs = IfUseUnfoldingRhs | IfRhs IfaceExpr
