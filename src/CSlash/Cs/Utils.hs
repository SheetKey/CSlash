{-# LANGUAGE ConstraintKinds #-}

module CSlash.Cs.Utils
  (
    unguardedGRHSs, unguardedRHS
  , mkMatchGroup, mkLamMatchGroup, mkTyLamTyMatchGroup, mkCsIf

  , missingTupArg

  , mkNPat

  , csTypeToCsSigType
  ) where

import CSlash.Cs.Decls
import CSlash.Cs.Binds
import CSlash.Cs.Expr
import CSlash.Cs.Pat
import CSlash.Cs.Type
import CSlash.Cs.Lit
import CSlash.Language.Syntax.Decls
import CSlash.Language.Syntax.Extension
import CSlash.Cs.Extension
import CSlash.Parser.Annotation

import CSlash.Core.DataCon
import CSlash.Core.Type ( Type )

import CSlash.Types.Id
import CSlash.Types.Name
import CSlash.Types.Name.Set hiding ( unitFV )
import CSlash.Types.Name.Env
import CSlash.Types.Name.Reader
import CSlash.Types.Var
import CSlash.Types.Basic
import CSlash.Types.SrcLoc
import CSlash.Types.Fixity
import CSlash.Types.SourceText

import CSlash.Data.FastString
import CSlash.Data.Bag

import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Control.Arrow ( first )
import Data.Foldable ( toList )
import Data.List ( partition )
import Data.List.NonEmpty ( nonEmpty )
import qualified Data.List.NonEmpty as NE

import Data.IntMap ( IntMap )
import qualified Data.IntMap.Strict as IntMap
import Data.Map ( Map )
import qualified Data.Map.Strict as Map

{- *********************************************************************
*                                                                      *
        Some useful helpers for constructing syntax
*                                                                      *
********************************************************************* -}

unguardedGRHSs
  :: Anno (GRHS (CsPass p) (LocatedA (body (CsPass p))))
     ~ EpAnn NoEpAnns
  => SrcSpan
  -> LocatedA (body (CsPass p))
  -> EpAnn GrhsAnn
  -> GRHSs (CsPass p) (LocatedA (body (CsPass p)))
unguardedGRHSs loc rhs an = GRHSs emptyComments (unguardedRHS an loc rhs)

unguardedRHS
  :: Anno (GRHS (CsPass p) (LocatedA (body (CsPass p))))
     ~ EpAnn NoEpAnns
  => EpAnn GrhsAnn
  -> SrcSpan
  -> LocatedA (body (CsPass p))
  -> [LGRHS (CsPass p) (LocatedA (body (CsPass p)))]
unguardedRHS an loc rhs = [L (noAnnSrcSpan loc) (GRHS an [] rhs)]

type AnnoBody p body
  = ( XMG (CsPass p) (LocatedA (body (CsPass p))) ~ Origin
    , Anno [LocatedA (Match (CsPass p) (LocatedA (body (CsPass p))))] ~ SrcSpanAnnL
    , Anno (Match (CsPass p) (LocatedA (body (CsPass p)))) ~ SrcSpanAnnA
    )

mkMatchGroup
  :: AnnoBody p body
  => Origin
  -> LocatedL [LocatedA (Match (CsPass p) (LocatedA (body (CsPass p))))]
  -> MatchGroup (CsPass p) (LocatedA (body (CsPass p)))
mkMatchGroup origin matches = MG { mg_ext = origin
                                 , mg_alts = matches }

mkLamMatchGroup
  :: AnnoBody p body
  => Origin
  -> LocatedL [LocatedA (Match (CsPass p) (LocatedA (body (CsPass p))))]
  -> MatchGroup (CsPass p) (LocatedA (body (CsPass p)))
mkLamMatchGroup origin (L l matches)
  = mkMatchGroup origin (L l $ map fixCtxt matches)
  where
    fixCtxt (L a match) = L a match{ m_ctxt = LamAlt }

mkTyLamTyMatchGroup
  :: AnnoBody p body
  => Origin
  -> LocatedL [LocatedA (Match (CsPass p) (LocatedA (body (CsPass p))))]
  -> MatchGroup (CsPass p) (LocatedA (body (CsPass p)))
mkTyLamTyMatchGroup origin (L l matches)
  = mkMatchGroup origin (L l $ map fixCtxt matches)
  where
    fixCtxt (L a match) = L a match{ m_ctxt = TyLamTyAlt }

mkCsIf :: LCsExpr Ps -> LCsExpr Ps -> LCsExpr Ps -> AnnsIf -> CsExpr Ps
mkCsIf c a b anns = CsIf anns c a b

mkNPat :: LocatedAn NoEpAnns (CsOverLit Ps) -> Maybe (SyntaxExpr Ps) -> [AddEpAnn] -> Pat Ps
mkNPat lit neg anns = NPat anns lit neg noSyntaxExpr

missingTupArg :: EpAnn Bool -> CsTupArg Ps
missingTupArg ann = Missing ann

{- *********************************************************************
*                                                                      *
        LCsSigType
*                                                                      *
********************************************************************* -}

csTypeToCsSigType :: LCsType Ps -> LCsSigType Ps
csTypeToCsSigType lty@(L loc ty) =
  L (l2l loc) $ CsSig noExtField lty
