module CSlash.Types.SourceText
  ( module X
  , pprWithSourceText
  ) where

import GHC.Types.SourceText as X hiding
  (pprWithSourceText)

import CSlash.Utils.Outputable

pprWithSourceText :: SourceText -> SDoc -> SDoc
pprWithSourceText NoSourceText d = d
pprWithSourceText (SourceText src) _ = ftext src


mkRationalWithExponentBase :: Rational -> Integer -> FractionalExponentBase -> Rational
mkRationalWithExponentBase i e feb = i * (eb ^^ e)
  where eb = case feb of Base2 -> 2 ; Base10 -> 10

instance Outputable StringLiteral where
  ppr sl = pprWithSourceText (sl_st sl) (doubleQuotes $ ftext $ sl_fs sl)

instance Outputable FractionalLit where
  ppr fl@(FL {}) =
    pprWithSourceText (fl_text fl) $
    rational $ mkRationalWithExponentBase (fl_signi fl) (fl_exp fl) (fl_exp_base fl)

