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

import {-# SOURCE #-} CSlash.Core.Type.Rep    ( Type )
-- import CSlash.Core.DataCon ( splitDataProductType_maybe, StrictnessMark, isMarkedStrict )
-- import GHC.Core.Multiplicity    ( scaledThing )

import CSlash.Utils.Binary
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Data.Coerce (coerce)
import Data.Function

{- *********************************************************************
*                                                                      *
           Card
*                                                                      *
********************************************************************* -}

data Card
  = C_10 -- Strict, not used
  | C_11 -- Strict, used at most once
  | C_1N -- Strict, no usage information
  deriving Eq

-- C_11 or C_1N
type CardNonAbs = Card 

-- C_10 or C_1N
type CardNonOnce = Card

_botCard :: Card
_botCard = C_10

topCard :: Card
topCard = C_1N

isAbs :: Card -> Bool
isAbs C_10 = True
isAbs _ = False

isAtMostOnce :: Card -> Bool
isAtMostOnce C_1N = False
isAtMostOnce _ = True

isCardNonAbs :: Card -> Bool
isCardNonAbs = not . isAbs

isCardNonOnce :: Card -> Bool
isCardNonOnce n = isAbs n || not (isAtMostOnce n)

multCard :: Card -> Card -> Card
multCard C_10 C_10 = C_10
multCard C_10 C_11 = C_10
multCard C_10 C_1N = C_10
multCard C_11 C_11 = C_11
multCard C_11 C_1N = C_1N
multCard C_1N C_1N = C_1N
multCard b a = multCard a b

{- *********************************************************************
*                                                                      *
           Demand: Evaluation contexts
*                                                                      *
********************************************************************** -}

data Demand
  = BotDmd
  | D !CardNonAbs !SubDemand
  deriving Eq

viewDmdPair :: Demand -> (Card, SubDemand)
viewDmdPair BotDmd = (C_10, botSubDmd)
viewDmdPair (D n sd) = (n, sd)

pattern (:*) :: HasDebugCallStack => Card -> SubDemand -> Demand
pattern n :* sd <- (viewDmdPair -> (n, sd)) where
  C_10 :* sd = BotDmd & assertPpr (sd == botSubDmd) (text "B /=" <+> ppr sd)
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

botSubDmd :: SubDemand
botSubDmd = Poly C_10

topSubDmd :: SubDemand
topSubDmd = Poly C_1N

polyFieldDmd :: CardNonOnce -> Demand
polyFieldDmd C_10 = BotDmd
polyFieldDmd n = n :* Poly n & assertPpr (isCardNonOnce n) (ppr n)

mkProd :: [Demand] -> SubDemand
mkProd ds
  | all (== BotDmd) ds = Poly C_10
  | dmd@(n :* Poly m) : _ <- ds
  , n == m
  , all (== dmd) ds
  = Poly n
  | otherwise = Prod ds

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
topDmd = C_1N :* topSubDmd

botDmd :: Demand
botDmd = BotDmd

multDmd :: Card -> Demand -> Demand
multDmd C_11 dmd = dmd
multDmd C_10 (D {}) = BotDmd
multDmd _ BotDmd = BotDmd
multDmd n (D m sd) = multCard n m :* multSubDmd n sd

multSubDmd :: Card -> SubDemand -> SubDemand
multSubDmd C_11 sd = sd
multSubDmd C_10 (Poly {}) = botSubDmd
multSubDmd C_10 (Call {}) = botSubDmd
multSubDmd n (Poly m) = Poly (multCard n m)
multSubDmd n (Call m sd) = mkCall (multCard n m) sd
multSubDmd n (Prod ds) = mkProd (strictMap (multDmd n) ds)

floatifyDmd :: Demand -> Demand
floatifyDmd = multDmd C_1N

peelManyCalls :: Arity -> SubDemand -> (Bool, Card, SubDemand)
peelManyCalls k sd = go k C_11 sd
  where
    go 0 !n !sd = (True, n, sd)
    go k !n (viewCall -> Just (m, sd)) = go (k-1) (n `multCard` m) sd
    go _ _ _ = (False, topCard, topSubDmd)

argsOneShots :: DmdSig -> Arity -> [[OneShotInfo]]
argsOneShots (DmdSig (DmdType _ arg_ds)) n_val_args
  | unsaturated_call = []
  | otherwise = go arg_ds
  where
    unsaturated_call = arg_ds `lengthExceeds` n_val_args

    go [] = []
    go (arg_d : arg_ds) = argOneShots arg_d `cons` go arg_ds

    cons [] [] = []
    cons a as = a:as

argOneShots :: Demand -> [OneShotInfo]
argOneShots BotDmd = []
argOneShots (_ :* sd) = map go (callCards sd)
  where
    go n | isAtMostOnce n = OneShotLam
         | otherwise = NoOneShotInfo

callCards :: SubDemand -> [Card]
callCards (Call n sd) = n : callCards sd
callCards (Poly _) = []
callCards Prod{} = []

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

topDiv :: Divergence
topDiv = Dunno

botDiv :: Divergence
botDiv = Diverges

isDeadEndDiv :: Divergence -> Bool
isDeadEndDiv Diverges = True
isDeadEndDiv ExnOrDiv = True
isDeadEndDiv Dunno = False

defaultFvDmd :: Divergence -> Demand
defaultFvDmd Dunno = botDmd
defaultFvDmd ExnOrDiv = botDmd
defaultFvDmd Diverges = botDmd

defaultArgDmd :: Divergence -> Demand
defaultArgDmd Dunno = topDmd
defaultArgDmd ExnOrDiv = panic "absDmd"
defaultArgDmd Diverges = botDmd

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

mkEmptyDmdEnv :: Divergence -> DmdEnv
mkEmptyDmdEnv div = DE emptyVarEnv div

nopDmdEnv :: DmdEnv
nopDmdEnv = mkEmptyDmdEnv topDiv

nopDmdType :: DmdType
nopDmdType = DmdType nopDmdEnv []

dmdTypeDepth :: DmdType -> Arity
dmdTypeDepth = length . dt_args

etaExpandDmdType :: Arity -> DmdType -> DmdType
etaExpandDmdType n d@DmdType { dt_args = ds, dt_env = env }
  | n == depth = d
  | n > depth = d { dt_args = inc_ds }
  | otherwise = pprPanic "etaExpandDmdType: arity decrease" (ppr n $$ ppr d)
  where
    depth = length ds
    inc_ds = take n (ds ++ repeat (defaultArgDmd (de_div env)))

{- *********************************************************************
*                                                                      *
                     Demand signatures
*                                                                      *
********************************************************************* -}

newtype DmdSig = DmdSig DmdType
  deriving Eq

mkDmdSigForArity :: Arity -> DmdType -> DmdSig
mkDmdSigForArity threshold_arity dmd_ty@(DmdType fvs args)
  | threshold_arity < dmdTypeDepth dmd_ty
  = DmdSig $ DmdType (fvs { de_div = topDiv }) (take threshold_arity args)
  | otherwise
  = DmdSig (etaExpandDmdType threshold_arity dmd_ty)

mkClosedDmdSig :: [Demand] -> Divergence -> DmdSig
mkClosedDmdSig ds div = mkDmdSigForArity (length ds) (DmdType (mkEmptyDmdEnv div) ds)

mkVanillaDmdSig :: Arity -> Divergence -> DmdSig
mkVanillaDmdSig ar div = mkClosedDmdSig (replicate ar topDmd) div

splitDmdSig :: DmdSig -> ([Demand], Divergence)
splitDmdSig (DmdSig (DmdType env dmds)) = (dmds, de_div env)

nopSig :: DmdSig
nopSig = DmdSig nopDmdType

isDeadEndSig :: DmdSig -> Bool
isDeadEndSig (DmdSig (DmdType env _)) = isDeadEndDiv (de_div env)

prependArgsDmdSig :: Int -> DmdSig -> DmdSig
prependArgsDmdSig new_args sig@(DmdSig dmd_ty@(DmdType env dmds))
  | new_args == 0 = sig
  | dmd_ty == nopDmdType = sig
  | otherwise = DmdSig (DmdType env dmds')
  where
    dmds' = assertPpr (new_args > 0) (ppr new_args)
            $ replicate new_args topDmd ++ dmds

{- *********************************************************************
*                                                                      *
                     Outputable and Binary instances
*                                                                      *
********************************************************************* -}

instance Show Card where
  show C_10 = "C_10"
  show C_11 = "C_11"
  show C_1N = "C_1N"

instance Outputable Card where
  ppr C_11 = char '1' -- "exactly 1"
  ppr C_1N = char 'S' -- "Strict"
  ppr C_10 = char 'B' -- "Bottom"

instance Outputable Demand where
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
  put_ bh C_11 = putByte bh 1
  put_ bh C_1N = putByte bh 2
  put_ bh C_10 = putByte bh 3
  get bh = do
    h <- getByte bh
    case h of
      1 -> return C_11
      2 -> return C_1N
      3 -> return C_10
      _ -> pprPanic "Binary:Card" (ppr (fromIntegral h :: Int))

instance Binary Demand where
  put_ bh (n :* sd) = put_ bh n *> case n of
    C_10 -> return ()
    _    -> put_ bh sd
  get bh = get bh >>= \n -> case n of
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

{- *********************************************************************
*                                                                      *
                     Demand transformers
*                                                                      *
********************************************************************* -}

zapDmdEnv :: DmdEnv -> DmdEnv
zapDmdEnv (DE _ div) = mkEmptyDmdEnv div

zapDmdEnvSig :: DmdSig -> DmdSig
zapDmdEnvSig (DmdSig (DmdType env ds)) = DmdSig (DmdType (zapDmdEnv env) ds)
