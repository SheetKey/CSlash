{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveFunctor #-}

module CSlash.CsToCore.Pmc.Types
  ( module CSlash.CsToCore.Pmc.Types
  , module CSlash.CsToCore.Pmc.Solver.Types
  ) where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.CsToCore.Pmc.Solver.Types

import CSlash.Data.OrdList
import CSlash.Types.Var
-- import CSlash.Types.Var (EvVar)
import CSlash.Types.SrcLoc
import CSlash.Utils.Outputable
import CSlash.Core.ConLike
import CSlash.Core.Type
import CSlash.Core

import Data.List.NonEmpty ( NonEmpty(..) )
import qualified Data.List.NonEmpty as NE
import qualified Data.Semigroup as Semi

data PmGrd
  = PmCon { pm_id :: !(Id Zk) -- WILL CHANGE! (Wait until we type check pats)
          , pm_con_con :: !PmAltCon
          , pm_con_tvs :: ![TyVar Zk]
          , pm_con_args :: ![Id Zk]
          }
  | PmLet { pm_id :: !(Id Zk)
          , _pm_let_expr :: !CoreExpr
          }

instance Outputable PmGrd where
  ppr (PmCon x alt _ con_args) = hsep [ ppr alt, hsep (map ppr con_args), text "<-", ppr x ]
  ppr (PmLet x expr) = hsep [ text "let", ppr x, text "=", ppr expr ]

newtype SrcInfo = SrcInfo (Located SDoc)

data GrdDag -- TODO: Add OrPatterns!
  = GdEnd
  | GdOne !PmGrd
  | GdSeq !GrdDag !GrdDag
  | GdAlt !GrdDag !GrdDag

sequencePmGrds :: [PmGrd] -> GrdDag
sequencePmGrds = sequenceGrdDags . map GdOne

sequenceGrdDags :: [GrdDag] -> GrdDag
sequenceGrdDags xs = foldr gdSeq GdEnd xs

consGrdDag :: PmGrd -> GrdDag -> GrdDag
consGrdDag g d = gdSeq (GdOne g) d

gdSeq :: GrdDag -> GrdDag -> GrdDag
gdSeq g1 GdEnd = g1
gdSeq GdEnd g2 = g2
gdSeq g1 g2 = g1 `GdSeq` g2

newtype PmMatchGroup p = PmMatchGroup (NonEmpty (PmMatch p))

data PmMatch p = PmMatch { pm_pats :: !p, pm_grhss :: !(PmGRHSs p) }

data PmGRHSs p = PmGRHSs { pgs_grhss :: !(NonEmpty (PmGRHS p)) }

data PmGRHS p = PmGRHS { pg_grds :: !p, pg_rhs :: !SrcInfo }

instance Outputable SrcInfo where
  ppr (SrcInfo (L (RealSrcSpan rss _) _)) = ppr (srcSpanStartLine rss)
  ppr (SrcInfo (L s _)) = ppr s

instance Outputable GrdDag where
  ppr GdEnd = empty
  ppr (GdOne g) = ppr g
  ppr (GdSeq d1 d2) = ppr d1 <> comma <+> ppr d2
  ppr d0@GdAlt{} = parens $ fsep (ppr d : map ((semi <+>) . ppr) ds)
    where
      d NE.:| ds = collect d0
      collect (GdAlt d1 d2) = collect d1 Semi.<> collect d2
      collect d = NE.singleton d

pprLygSequence :: Outputable a => NonEmpty a -> SDoc
pprLygSequence (NE.toList -> as)
  = braces (space <> fsep (punctuate semi (map ppr as)) <> space)

instance Outputable p => Outputable (PmMatchGroup p) where
  ppr (PmMatchGroup matches) = pprLygSequence matches

instance Outputable p => Outputable (PmMatch p) where
  ppr (PmMatch { pm_pats = grds, pm_grhss = grhss })
    = ppr grds <+> ppr grhss

instance Outputable p => Outputable (PmGRHSs p) where
  ppr (PmGRHSs { pgs_grhss = grhss }) = ppr grhss

instance Outputable p => Outputable (PmGRHS p) where
  ppr (PmGRHS { pg_grds = grds, pg_rhs = rhs })
    = ppr grds <+> text "->" <+> ppr rhs

data Precision = Approximate | Precise
  deriving (Eq, Show)

instance Semi.Semigroup Precision where
  Precise <> Precise = Precise
  _ <> _ = Approximate

instance Monoid Precision where
  mempty = Precise
  mappend = (Semi.<>)

data RedSets = RedSets
  { rs_cov :: !Nablas
  , rs_div :: !Nablas
  }

instance Outputable RedSets where
  ppr _ = empty

data CheckResult a = CheckResult
  { cr_ret :: !a
  , cr_uncov :: !Nablas
  , cr_approx :: !Precision
  } deriving Functor

instance Outputable a => Outputable (CheckResult a) where
  ppr (CheckResult c unc pc)
    = text "CheckResult" <+> ppr_precision pc <+> braces (fsep [ field "ret" c <> comma
                                                               , field "uncov" unc ])
    where
      ppr_precision Precise = empty
      ppr_precision Approximate = text "(Approximate)"
      field name value = text name <+> equals <+> ppr value

type Pre = GrdDag
type Post = RedSets
