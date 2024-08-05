module CSlash.Cs.Utils where

import CSlash.Hs.Decls
import CSlash.Hs.Binds
import CSlash.Hs.Expr
import CSlash.Hs.Pat
import CSlash.Hs.Type
import CSlash.Hs.Lit
import CSlash.Language.Syntax.Decls
import CSlash.Language.Syntax.Extension
import CSlash.Hs.Extension
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
