{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE PatternSynonyms #-}

module CSlash.Types.Demand where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Unique.FM
import CSlash.Types.Basic
import CSlash.Data.Maybe   ( orElse )

import CSlash.Core.Type    ( Type{-, isTerminatingType-} )
-- import CSlash.Core.DataCon ( splitDataProductType_maybe, StrictnessMark, isMarkedStrict )
-- import GHC.Core.Multiplicity    ( scaledThing )

import CSlash.Utils.Binary
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Data.Coerce (coerce)
import Data.Function

import Data.Bits ((.&.))

{- *********************************************************************
*                                                                      *
           Card
*                                                                      *
********************************************************************* -}

newtype Card = Card Int
  deriving Eq

type CardNonAbs = Card

type CardNonOnce = Card

pattern C_00 :: Card
pattern C_00 = Card 0b001

pattern C_10 :: Card
pattern C_10 = Card 0b000

pattern C_11 :: Card
pattern C_11 = Card 0b010

pattern C_01 :: Card
pattern C_01 = Card 0b011

pattern C_1N :: Card
pattern C_1N = Card 0b110

pattern C_0N :: Card
pattern C_0N = Card 0b111

{-# COMPLETE C_00, C_01, C_0N, C_10, C_11, C_1N :: Card #-}

_botCard :: Card
_botCard = C_10

topCard :: Card
topCard = C_0N

isAbs :: Card -> Bool
isAbs (Card c) = c .&. 0b110 == 0

isAtMostOnce :: Card -> Bool
isAtMostOnce (Card c) = c .&. 0b100 == 0

isCardNonAbs :: Card -> Bool
isCardNonAbs = not . isAbs

isCardNonOnce :: Card -> Bool
isCardNonOnce n = isAbs n || not (isAtMostOnce n)

{- *********************************************************************
*                                                                      *
           Demand: Evaluation contexts
*                                                                      *
********************************************************************** -}

data Demand
  = BotDmd
  | AbsDmd
  | D !CardNonAbs !SubDemand
  deriving Eq

viewDmdPair :: Demand -> (Card, SubDemand)
viewDmdPair BotDmd = (C_10, botSubDmd)
viewDmdPair AbsDmd = (C_00, botSubDmd)
viewDmdPair (D n sd) = (n, sd)

pattern (:*) :: HasDebugCallStack => Card -> SubDemand -> Demand
pattern n :* sd <- (viewDmdPair -> (n, sd)) where
  C_10 :* sd = BotDmd & assertPpr (sd == botSubDmd) (text "B /=" <+> ppr sd)
  C_00 :* sd = AbsDmd & assertPpr (sd == botSubDmd) (text "A /=" <+> ppr sd)
  n :* sd = D n sd & assertPpr (isCardNonAbs n) (ppr n $$ ppr sd)

{-# COMPLETE (:*) #-}

data SubDemand
  = Poly !CardNonOnce
  | Call !CardNonAbs !SubDemand
  | Prod ![Demand]

instance Eq SubDemand where
  d1 == d2 = case d1 of
    Prod ds1
      | Just ds2 <- viewProd (length ds1) d2 -> ds1 == ds2
    Call n1 sd1
      | Just (n2, sd2) <- viewCall d2 -> n1 == n2 && sd1 == sd2
    Poly n1
      | Poly n2 <- d2 -> n1 == n2
    _ -> False

topSubDmd :: SubDemand
topSubDmd = Poly C_0N

botSubDmd :: SubDemand
botSubDmd = Poly C_10

polyFieldDmd :: CardNonOnce -> Demand
polyFieldDmd C_00 = AbsDmd
polyFieldDmd C_10 = BotDmd
polyFieldDmd n = n :* Poly n & assertPpr (isCardNonOnce n) (ppr n)

viewProd :: Arity -> SubDemand -> Maybe [Demand]
viewProd n (Prod ds)
  | ds `lengthIs` n = Just ds
viewProd n (Poly card)
  | let !ds = replicate n $! polyFieldDmd card
  = Just ds
viewProd _ _ = Nothing
{-# INLINE viewProd #-}

mkCall :: CardNonAbs -> SubDemand -> SubDemand
mkCall n sd = assertPpr (isCardNonAbs n) (ppr n $$ ppr sd) $ Call n sd

viewCall :: SubDemand -> Maybe (Card, SubDemand)
viewCall (Call n sd) = Just (n :: Card, sd)
viewCall (Poly n)
  | isAbs n = Just (n :: Card, botSubDmd)
viewCall _ = Nothing

topDmd :: Demand
topDmd = C_0N :* topSubDmd

absDmd :: Demand
absDmd = AbsDmd

botDmd :: Demand
botDmd = BotDmd

{- *********************************************************************
*                                                                      *
                 Divergence: Whether evaluation surely diverges
*                                                                      *
********************************************************************* -}

data Divergence
  = Diverges
  | ExnOrDiv
  | Dunno
  deriving Eq

defaultFvDmd :: Divergence -> Demand
defaultFvDmd Dunno = absDmd
defaultFvDmd ExnOrDiv = absDmd
defaultFvDmd Diverges = botDmd

{- *********************************************************************
*                                                                      *
           Demand environments and types
*                                                                      *
********************************************************************* -}

data DmdEnv = DE
  { de_fvs :: !(VarEnv (Id Zk) Demand)
  , de_div :: !Divergence
  }

instance Eq DmdEnv where
  DE fv1 div1 == DE fv2 div2
    = div1 == div2 && canonicalise div1 fv1 == canonicalise div2 fv2
    where
      canonicalise div fv = filterUFM (/= defaultFvDmd div) fv

data DmdType = DmdType
  { dt_env :: !DmdEnv
  , dt_args :: ![Demand]
  }

instance Eq DmdType where
  DmdType env1 ds1 == DmdType env2 ds2
    = ds1 == ds2 && env1 == env2

{- *********************************************************************
*                                                                      *
                     Demand signatures
*                                                                      *
********************************************************************* -}

newtype DmdSig = DmdSig DmdType
  deriving Eq

{- *********************************************************************
*                                                                      *
                     Outputable and Binary instances
*                                                                      *
********************************************************************* -}

instance Show Card where
  show C_00 = "C_00"
  show C_01 = "C_01"
  show C_0N = "C_0N"
  show C_10 = "C_01"
  show C_11 = "C_11"
  show C_1N = "C_1N"

instance Outputable Card where
  ppr C_00 = char 'A' -- "Absent"
  ppr C_01 = char 'M' -- "Maybe"
  ppr C_0N = char 'L' -- "Lazy"
  ppr C_11 = char '1' -- "exactly 1"
  ppr C_1N = char 'S' -- "Strict"
  ppr C_10 = char 'B' -- "Bottom"

instance Outputable Demand where
  ppr AbsDmd                    = char 'A'
  ppr BotDmd                    = char 'B'
  ppr (n :* sd)                 = ppr n <> ppr sd

instance Outputable SubDemand where
  ppr (Poly n) = ppr n
  ppr (Call n sd) = char 'C' <> parens (ppr n <> comma <> ppr sd)
  ppr (Prod ds) = char 'P' <> parens (fields ds)
    where
      fields []     = empty
      fields [x]    = ppr x
      fields (x:xs) = ppr x <> char ',' <> fields xs

instance Outputable Divergence where
  ppr Diverges = char 'b' -- for (b)ottom
  ppr ExnOrDiv = char 'x' -- for e(x)ception
  ppr Dunno    = empty

instance Outputable DmdEnv where
  ppr (DE fvs div)
    = ppr div <> if null fv_elts then empty
                 else braces (fsep (map pp_elt fv_elts))
    where
      pp_elt (uniq, dmd) = ppr uniq <> text "->" <> ppr dmd
      fv_elts = nonDetUFMToList fvs

instance Outputable DmdType where
  ppr (DmdType fv ds)
    = hcat (map (angleBrackets . ppr) ds) <> ppr fv

instance Outputable DmdSig where
   ppr (DmdSig ty) = ppr ty

instance Binary Card where
  put_ bh C_00 = putByte bh 0
  put_ bh C_01 = putByte bh 1
  put_ bh C_0N = putByte bh 2
  put_ bh C_11 = putByte bh 3
  put_ bh C_1N = putByte bh 4
  put_ bh C_10 = putByte bh 5
  get bh = do
    h <- getByte bh
    case h of
      0 -> return C_00
      1 -> return C_01
      2 -> return C_0N
      3 -> return C_11
      4 -> return C_1N
      5 -> return C_10
      _ -> pprPanic "Binary:Card" (ppr (fromIntegral h :: Int))

instance Binary Demand where
  put_ bh (n :* sd) = put_ bh n *> case n of
    C_00 -> return ()
    C_10 -> return ()
    _    -> put_ bh sd
  get bh = get bh >>= \n -> case n of
    C_00 -> return AbsDmd
    C_10 -> return BotDmd
    _    -> (n :*) <$> get bh

instance Binary SubDemand where
  put_ bh (Poly sd) = putByte bh 0 *> put_ bh sd
  put_ bh (Call n sd) = putByte bh 1 *> put_ bh n *> put_ bh sd
  put_ bh (Prod ds) = putByte bh 2 *> put_ bh ds
  get bh = do
    h <- getByte bh
    case h of
      0 -> Poly <$> get bh
      1 -> mkCall <$> get bh <*> get bh
      2 -> Prod <$> get bh
      _ -> pprPanic "Binary:SubDemand" (ppr (fromIntegral h :: Int))

instance Binary Divergence where
  put_ bh Dunno    = putByte bh 0
  put_ bh ExnOrDiv = putByte bh 1
  put_ bh Diverges = putByte bh 2
  get bh = do
    h <- getByte bh
    case h of
      0 -> return Dunno
      1 -> return ExnOrDiv
      2 -> return Diverges
      _ -> pprPanic "Binary:Divergence" (ppr (fromIntegral h :: Int))

instance Binary DmdEnv where
  put_ bh (DE _ d) = put_ bh d
  get bh = DE emptyVarEnv <$> get bh

instance Binary DmdType where
  put_ bh (DmdType fv ds) = put_ bh fv *> put_ bh ds
  get bh = DmdType <$> get bh <*> get bh

instance Binary DmdSig where
  put_ bh (DmdSig aa) = put_ bh aa
  get bh = DmdSig <$> get bh
