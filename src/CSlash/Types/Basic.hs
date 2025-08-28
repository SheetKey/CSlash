{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Types.Basic
  ( ConTag

  , maybeParen

  , pprAlternative

  , TyConFlavor(..), tyConFlavorAssoc_maybe

  , module X
  ) where

import Prelude hiding ((<>))

import GHC.Types.Basic as X hiding
  ( TyConFlavour(..)
  , ConTag
  , pprAlternative
  , maybeParen
  , pprShortTailCallInfo
  , pprOneShotInfo
  )
  
import CSlash.Language.Syntax.Basic
import CSlash.Utils.Outputable

import Control.DeepSeq
import Data.Data

maybeParen :: PprPrec -> PprPrec -> SDoc -> SDoc
maybeParen ctxt_prec inner_prec pretty
  | ctxt_prec < inner_prec = pretty
  | otherwise = parens pretty

pprAlternative :: (a -> SDoc) -> a -> ConTag -> Arity -> SDoc
pprAlternative pp x alt arity
  = fsep (replicate (alt - 1) vbar ++ [pp x] ++ replicate (arity - alt) vbar)

data TyConFlavor
  = TupleFlavor
  | SumFlavor
  | DataTypeFlavor
  | AbstractTypeFlavor
  | TypeFunFlavor
  | BuiltInTypeFlavor
  deriving (Eq, Data)

instance Outputable TyConFlavor where
  ppr = text . go
    where
      go TupleFlavor = "tuple"
      go SumFlavor = "sum"
      go TypeFunFlavor = "type synonym"
      go DataTypeFlavor = "data type"
      go AbstractTypeFlavor = "abstract type"
      go BuiltInTypeFlavor = "built-in type"

instance NFData TyConFlavor where
  rnf TupleFlavor = ()
  rnf SumFlavor = ()
  rnf TypeFunFlavor = ()
  rnf DataTypeFlavor = ()
  rnf AbstractTypeFlavor = ()
  rnf BuiltInTypeFlavor = ()

tyConFlavorAssoc_maybe :: TyConFlavor -> Maybe tc
tyConFlavorAssoc_maybe _ = Nothing

instance Outputable TopLevelFlag where
  ppr TopLevel = text "<TopLevel>"
  ppr NotTopLevel = text "<NotTopLevel>"

instance Outputable SwapFlag where
  ppr IsSwapped = text "Is-swapped"
  ppr NotSwapped = text "Not-swapped"

instance Outputable RecFlag where
  ppr Recursive = text "Recursive"
  ppr NonRecursive = text "NonRecursive"

instance Outputable OccInfo where
  ppr (ManyOccs tails) = pprShortTailCallInfo tails
  ppr IAmDead = text "Dead"
  ppr (IAmALoopBreaker rule_only tails)
    = text "LoopBreaker" <> pp_ro <> pprShortTailCallInfo tails
    where pp_ro | rule_only = char '!'
                | otherwise = empty
  ppr (OneOcc inside_lam one_branch int_cxt tail_info)
    = text "Once" <> pp_lam inside_lam <> ppr one_branch <> pp_args int_cxt <> pp_tail
    where
      pp_lam IsInsideLam = char 'L'
      pp_lam NotInsideLam = empty
      pp_args IsInteresting = char '!'
      pp_args NotInteresting = empty
      pp_tail = pprShortTailCallInfo tail_info

pprShortTailCallInfo :: TailCallInfo -> SDoc
pprShortTailCallInfo (AlwaysTailCalled ar) = char 'T' <> brackets (int ar)
pprShortTailCallInfo NoTailCallInfo = empty

instance Outputable OneShotInfo where
  ppr = pprOneShotInfo

pprOneShotInfo :: OneShotInfo -> SDoc 
pprOneShotInfo NoOneShotInfo = text "NoOS"
pprOneShotInfo OneShotLam = text "OneShot"

instance Outputable UnfoldingSource where
  ppr CompulsorySrc = text "Compulsory"
  ppr StableUserSrc = text "StableUser"
  ppr StableSystemSrc = text "StableSystem"
  ppr VanillaSrc = text "<vanilla>"
