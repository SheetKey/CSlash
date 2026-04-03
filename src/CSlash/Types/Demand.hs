{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE PatternSynonyms #-}

module CSlash.Types.Demand where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Types.Var
import {-# SOURCE #-} CSlash.Types.Var.Id (Id)
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

oneifyCard :: Card -> Card 
oneifyCard = glbCard C_11

lubCard :: Card -> Card -> Card
lubCard C_10 c = c
lubCard c C_10 = c
lubCard C_11 c = c
lubCard c C_11 = c
lubCard C_1N C_1N = C_1N

glbCard :: Card -> Card -> Card
glbCard C_10 _ = C_10
glbCard _ C_10 = C_10
glbCard C_11 _ = C_11
glbCard _ C_11 = C_11
glbCard C_1N C_1N = C_1N

plusCard :: Card -> Card -> Card
plusCard C_10 c = c
plusCard c C_10 = c
plusCard _ _ = C_1N

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

seqSubDmd :: SubDemand
seqSubDmd = Poly C_10 -- TODO: What??

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

lubDmd :: Demand -> Demand -> Demand
lubDmd BotDmd dmd2 = dmd2
lubDmd dmd1 BotDmd = dmd1
lubDmd (n1 :* sd1) (n2 :* sd2) = lubCard n1 n2 :* lubSubDmd sd1 sd2

lubSubDmd :: SubDemand -> SubDemand -> SubDemand
lubSubDmd (Poly C_10) sd = sd
lubSubDmd sd (Poly C_10) = sd
lubSubDmd (Prod ds1) (Poly n2) = let !d = polyFieldDmd n2 in mkProd (strictMap (lubDmd d) ds1)
lubSubDmd (Prod ds1) (Prod ds2)
  | equalLength ds1 ds2
  = mkProd (strictZipWith lubDmd ds1 ds2)
lubSubDmd (Call n1 sd1) (viewCall -> Just (n2, sd2)) = mkCall (lubCard n1 n2) (lubSubDmd sd1 sd2)
lubSubDmd (Poly n1) (Poly n2) = Poly (lubCard n1 n2)
lubSubDmd sd1@Poly{} sd2 = lubSubDmd sd2 sd1
lubSubDmd _ _ = topSubDmd

plusDmd :: Demand -> Demand -> Demand
plusDmd (n1 :* sd1) (n2 :* sd2)
  = plusCard n1 n2 :* plusSubDmd sd1 sd2

plusSubDmd :: SubDemand -> SubDemand -> SubDemand
plusSubDmd (Prod ds1) (Poly n2)
  = let !d = polyFieldDmd n2 in mkProd (strictMap (plusDmd d) ds1)
plusSubDmd (Prod ds1) (Prod ds2)
  | equalLength ds1 ds2
  = mkProd (strictZipWith plusDmd ds1 ds2)
plusSubDmd (Call n1 sd1) (viewCall -> Just (n2, sd2))
  = mkCall (plusCard n1 n2) (lubSubDmd sd1 sd2)
plusSubDmd (Poly n1) (Poly n2) = Poly (plusCard n1 n2)
plusSubDmd sd1@Poly{} sd2 = plusSubDmd sd2 sd1
plusSubDmd _ _ = topSubDmd

floatifyDmd :: Demand -> Demand
floatifyDmd = multDmd C_1N

mkCalledOnceDmd :: SubDemand -> SubDemand
mkCalledOnceDmd sd = mkCall C_11 sd

mkCalledOnceDmds :: Arity -> SubDemand -> SubDemand
mkCalledOnceDmds arity sd = iterate mkCalledOnceDmd sd !! arity

peelCallDmd :: SubDemand -> (Card, SubDemand)
peelCallDmd sd = viewCall sd `orElse` (topCard, topSubDmd)

-- The bool is my addition: True => saturated function call
peelManyCalls :: Arity -> SubDemand -> (Bool, Card, SubDemand)
peelManyCalls k sd = go k C_11 sd
  where
    go 0 !n !sd = (True, n, sd)
    go k !n (viewCall -> Just (m, sd)) = go (k-1) (n `multCard` m) sd
    go _ _ _ = (False, topCard, topSubDmd)
{-# INLINE peelManyCalls #-}

strictCallArity :: SubDemand -> Arity
strictCallArity sd = go 0 sd
  where
    go n (Call card sd) = go (n + 1) sd
    go n _ = n

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

lubDivergence :: Divergence -> Divergence -> Divergence
lubDivergence Diverges div = div
lubDivergence div Diverges = div
lubDivergence ExnOrDiv ExnOrDiv = ExnOrDiv
lubDivergence _ _ = Dunno

plusDivergence :: Divergence -> Divergence -> Divergence
plusDivergence Dunno Dunno = Dunno
plusDivergence Diverges _ = Diverges
plusDivergence _ Diverges = Diverges
plusDivergence _ _ = ExnOrDiv

multDivergence :: Card -> Divergence -> Divergence
multDivergence _ d = d

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

multDmdEnv :: Card -> DmdEnv -> DmdEnv
multDmdEnv C_11 env = env
multDmdEnv n (DE fvs div) = DE (mapVarEnv (multDmd n) fvs) (multDivergence n div)

reuseEnv :: DmdEnv -> DmdEnv
reuseEnv = multDmdEnv C_1N

lookupDmdEnv :: DmdEnv -> Id Zk -> Demand
lookupDmdEnv (DE fv div) id = lookupVarEnv fv id `orElse` defaultFvDmd div

delDmdEnv :: DmdEnv -> Id Zk -> DmdEnv
delDmdEnv (DE fv div) id = DE (fv `delVarEnv` id) div

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

botDmdEnv :: DmdEnv
botDmdEnv = mkEmptyDmdEnv botDiv

lubDmdEnv :: DmdEnv -> DmdEnv -> DmdEnv
lubDmdEnv (DE fv1 d1) (DE fv2 d2) = DE lub_fv lub_div
  where
    lub_fv = plusVarEnv_CD lubDmd fv1 (defaultFvDmd d1) fv2 (defaultFvDmd d2)
    lub_div = lubDivergence d1 d2

addVarDmdEnv :: DmdEnv -> Id Zk -> Demand -> DmdEnv
addVarDmdEnv env@(DE fvs div) id dmd
  = DE (extendVarEnv fvs id (dmd `plusDmd` lookupDmdEnv env id)) div

plusDmdEnv :: DmdEnv -> DmdEnv -> DmdEnv
plusDmdEnv (DE fv1 d1) (DE fv2 d2)
  -- No absDmd!
  -- | isEmptyVarEnv fv2, defaultFvDmd d2 == absDmd
  -- = DE fv1 (d1 `plusDivergence` d2)
  -- | isEmptyVarEnv fv1, defaultFvDmd d1 == absDmd
  -- = DE fv2 (d1 `plusDivergence` d2)
  | otherwise
  = DE (plusVarEnv_CD plusDmd fv1 (defaultFvDmd d1) fv2 (defaultFvDmd d2))
       (d1 `plusDivergence` d2)

plusDmdEnvs :: [DmdEnv] -> DmdEnv
plusDmdEnvs [] = nopDmdEnv
plusDmdEnvs pdas = foldl1' plusDmdEnv pdas

lubDmdType :: DmdType -> DmdType -> DmdType
lubDmdType d1 d2 = DmdType lub_fv lub_ds
  where
    n = max (dmdTypeDepth d1) (dmdTypeDepth d2)
    (DmdType fv1 ds1) = etaExpandDmdType n d1
    (DmdType fv2 ds2) = etaExpandDmdType n d2
    lub_ds = zipWithEqual "lubDmdType" lubDmd ds1 ds2
    lub_fv = lubDmdEnv fv1 fv2

discardArgDmds :: DmdType -> DmdEnv
discardArgDmds (DmdType fv _) = fv

plusDmdType :: DmdType -> DmdEnv -> DmdType
plusDmdType (DmdType fv ds) fv'
  = DmdType (plusDmdEnv fv fv') ds

botDmdType :: DmdType
botDmdType = DmdType botDmdEnv []

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

splitDmdTy :: DmdType -> (Demand, DmdType)
splitDmdTy ty@DmdType{ dt_args = dmd : args } = (dmd, ty{ dt_args = args })
splitDmdTy ty@DmdType{ dt_env = env } = (defaultArgDmd (de_div env), ty)

multDmdType :: Card -> DmdType -> DmdType
multDmdType C_11 dmd_ty = dmd_ty
multDmdType n (DmdType fv args)
  = DmdType (multDmdEnv n fv) (strictMap (multDmd n) args)

peelFV :: DmdType -> Id Zk -> (DmdType, Demand)
peelFV (DmdType fv ds) id = (DmdType fv' ds, dmd)
  where
    !fv' = fv `delDmdEnv` id
    !dmd = lookupDmdEnv fv id

addDemand :: Demand -> DmdType -> DmdType
addDemand dmd (DmdType fv ds) = DmdType fv (dmd : ds)

findIdDemand :: DmdType -> Id Zk -> Demand
findIdDemand (DmdType fv _) id = lookupDmdEnv fv id

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

type DmdTransformer = SubDemand -> DmdType

dmdTransformSig :: DmdSig -> DmdTransformer
dmdTransformSig (DmdSig dmd_ty@(DmdType _ arg_ds)) sd
  = multDmdType (sndOf3 $ peelManyCalls (length arg_ds) sd) dmd_ty

dmdTransformDataConSig :: Arity -> DmdTransformer
dmdTransformDataConSig arity sd = case viewProd arity body_sd of
  Just dmds -> mk_body_ty n dmds
  Nothing -> nopDmdType
  where
    (_, n, body_sd) = peelManyCalls arity sd
    mk_body_ty n dmds = DmdType nopDmdEnv ((bump n) <$> dmds)
    bump n dmd = multDmd n (plusDmd (C_11 :* seqSubDmd) dmd)

zapDmdEnv :: DmdEnv -> DmdEnv
zapDmdEnv (DE _ div) = mkEmptyDmdEnv div

zapDmdEnvSig :: DmdSig -> DmdSig
zapDmdEnvSig (DmdSig (DmdType env ds)) = DmdSig (DmdType (zapDmdEnv env) ds)

{- *********************************************************************
*                                                                      *
        Sequencing demands
*                                                                      *
********************************************************************* -}

seqDemand :: Demand -> ()
seqDemand BotDmd = ()
seqDemand (_ :* sd) = seqSubDemand sd

seqSubDemand :: SubDemand -> ()
seqSubDemand (Prod ds) = seqDemandList ds
seqSubDemand (Call _ sd) = seqSubDemand sd
seqSubDemand (Poly _) = ()

seqDemandList :: [Demand] -> ()
seqDemandList = foldr (seq . seqDemand) ()

seqDmdType :: DmdType -> ()
seqDmdType (DmdType env ds) = seqDmdEnv env `seq` seqDemandList ds `seq` ()

seqDmdEnv :: DmdEnv -> ()
seqDmdEnv (DE fvs _) = seqEltsUFM seqDemand fvs

seqDmdSig :: DmdSig -> ()
seqDmdSig (DmdSig ty) = seqDmdType ty
