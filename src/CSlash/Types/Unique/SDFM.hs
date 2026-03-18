{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ApplicativeDo #-}
{-# OPTIONS_GHC -Wall #-}

module CSlash.Types.Unique.SDFM (
        UniqSDFM,

        emptyUSDFM,
        lookupUSDFM,
        equateUSDFM, addToUSDFM,
        traverseUSDFM
    ) where

import CSlash.Types.Unique
import CSlash.Types.Unique.DFM
import CSlash.Utils.Outputable

data Shared key ele
  = Indirect !key
  | Entry !ele

newtype UniqSDFM key ele
  = USDFM { unUSDFM :: UniqDFM key (Shared key ele) }

emptyUSDFM :: UniqSDFM key ele
emptyUSDFM = USDFM emptyUDFM

lookupReprAndEntryUSDFM :: Uniquable key => UniqSDFM key ele -> key -> (key, Maybe ele)
lookupReprAndEntryUSDFM (USDFM env) = go
  where
    go x = case lookupUDFM env x of
      Nothing           -> (x, Nothing)
      Just (Indirect y) -> go y
      Just (Entry ele)  -> (x, Just ele)

lookupUSDFM :: Uniquable key => UniqSDFM key ele -> key -> Maybe ele
lookupUSDFM usdfm x = snd (lookupReprAndEntryUSDFM usdfm x)

equateUSDFM
  :: Uniquable key => UniqSDFM key ele -> key -> key -> (Maybe ele, UniqSDFM key ele)
equateUSDFM usdfm@(USDFM env) x y =
  case (lu x, lu y) of
    ((x', _)    , (y', _))
      | getUnique x' == getUnique y' -> (Nothing, usdfm) -- nothing to do
    ((x', _)    , (y', Nothing))     -> (Nothing, set_indirect y' x')
    ((x', mb_ex), (y', _))           -> (mb_ex,   set_indirect x' y')
  where
    lu = lookupReprAndEntryUSDFM usdfm
    set_indirect a b = USDFM $ addToUDFM env a (Indirect b)

addToUSDFM :: Uniquable key => UniqSDFM key ele -> key -> ele -> UniqSDFM key ele
addToUSDFM usdfm@(USDFM env) x v =
  USDFM $ addToUDFM env (fst (lookupReprAndEntryUSDFM usdfm x)) (Entry v)

traverseUSDFM :: forall key a b f. Applicative f => (a -> f b) -> UniqSDFM key a -> f (UniqSDFM key b)
traverseUSDFM f = fmap (USDFM . listToUDFM_Directly) . traverse g . udfmToList . unUSDFM
  where
    g :: (Unique, Shared key a) -> f (Unique, Shared key b)
    g (u, Indirect y) = pure (u,Indirect y)
    g (u, Entry a)    = do
        a' <- f a
        pure (u,Entry a')

instance (Outputable key, Outputable ele) => Outputable (Shared key ele) where
  ppr (Indirect x) = ppr x
  ppr (Entry a)    = ppr a

instance (Outputable key, Outputable ele) => Outputable (UniqSDFM key ele) where
  ppr (USDFM env) = ppr env
