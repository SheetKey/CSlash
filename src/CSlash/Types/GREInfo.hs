{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}

module CSlash.Types.GREInfo where

import CSlash.Types.Basic
import CSlash.Types.Name
import CSlash.Types.Unique
import CSlash.Types.Unique.Set
import CSlash.Utils.Outputable as Out
import CSlash.Utils.Panic

import Control.DeepSeq
import Data.Data ( Data )
import Data.List.NonEmpty ( NonEmpty )
import qualified Data.List.NonEmpty as NonEmpty

data GREInfo
    = Vanilla
    | UnboundGRE
    | IAmTyCon !TyConFlavor
    | IAmKiCon !RowInfo
    | IAmConLike !ConInfo
    | IAmRow
      { rowLabel :: !Name
      , rowKiCon :: !Name }
    deriving Data

instance NFData GREInfo where
  rnf Vanilla = ()
  rnf UnboundGRE = ()
  rnf (IAmTyCon tc) = rnf tc
  rnf (IAmKiCon rows) = rnf rows
  rnf (IAmConLike info) = rnf info
  rnf (IAmRow a b) = rnf a `seq` rnf b

plusGREInfo :: GREInfo -> GREInfo -> GREInfo
plusGREInfo Vanilla Vanilla = Vanilla
plusGREInfo UnboundGRE UnboundGRE = UnboundGRE
plusGREInfo (IAmTyCon {})    info2@(IAmTyCon {}) = info2
plusGREInfo IAmKiCon{} info2@IAmKiCon{} = info2
plusGREInfo (IAmConLike {})  info2@(IAmConLike {}) = info2
plusGREInfo IAmRow{} info2@IAmRow{} = info2
plusGREInfo info1 info2 = pprPanic "plusInfo" $
  vcat [ text "info1:" <+> ppr info1
       , text "info2:" <+> ppr info2 ]

instance Outputable GREInfo where
  ppr Vanilla = text "Vanilla"
  ppr UnboundGRE = text "UnboundGRE"
  ppr (IAmTyCon flav)
    = text "TyCon" <+> ppr flav
  ppr (IAmKiCon rows) = text "KiCon" <+> ppr rows
  ppr (IAmConLike info)
    = text "ConLike" <+> ppr info
  ppr (IAmRow a b) = text "Row" <+> ppr b Out.<> dot Out.<> ppr a

data ConInfo
  = ConHasPositionalArgs
  | ConIsNullary
  deriving stock Eq
  deriving Data

instance NFData ConInfo where
  rnf ConHasPositionalArgs = ()
  rnf ConIsNullary = ()

mkConInfo :: Arity -> ConInfo
mkConInfo 0 = ConIsNullary
mkConInfo _ = ConHasPositionalArgs

instance Outputable ConInfo where
  ppr ConIsNullary = text "ConIsNullary"
  ppr ConHasPositionalArgs = text "ConHasPositionalArgs"

type RowInfo = NonEmpty Name
