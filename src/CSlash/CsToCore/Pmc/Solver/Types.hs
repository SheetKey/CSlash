module CSlash.CsToCore.Pmc.Solver.Types where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Data.Bag
import CSlash.Data.FastString
import CSlash.Types.Var.Class
import CSlash.Types.Var.Id
import CSlash.Types.Var.Set
import CSlash.Types.Unique.DSet
import CSlash.Types.Unique.SDFM
import CSlash.Types.Name
import CSlash.Core.DataCon
import CSlash.Core.ConLike hiding (eqConLike)
import CSlash.Utils.Outputable
import CSlash.Utils.Panic.Plain
import CSlash.Utils.Misc (lastMaybe)
import CSlash.Data.List.SetOps (unionLists)
import CSlash.Data.Maybe
import CSlash.Core.Type
import CSlash.Core.TyCon
import CSlash.Types.Literal
import CSlash.Core
import CSlash.Core.Type.Compare( eqType )
import CSlash.Core.Map.Expr
import CSlash.Core.Utils (exprType)
import CSlash.Builtin.Names
import CSlash.Builtin.Types
import CSlash.Builtin.Types.Prim
import CSlash.Tc.Solver.InertSet (InertTySet, emptyInert)
import CSlash.Tc.Utils.TcType (topTcLevel)
import CSlash.Types.CompleteMatch
import CSlash.Types.SourceText (SourceText(..), mkFractionalLit, FractionalLit
                            , fractionalLitFromRational
                            , FractionalExponentBase(..))
import Numeric (fromRat)
import Data.Foldable (find)
import Data.Ratio
import GHC.Real (Ratio(..))
import qualified Data.Semigroup as Semi

data Nabla = MkNabla
  { nabla_ty_st :: !TyState
  , nabla_tm_st :: !TmState
  }

initNabla :: Nabla
initNabla = MkNabla initTyState initTmState

instance Outputable Nabla where
  ppr nabla = hang (text "Nabla") 2
    $ vcat [ ppr (nabla_tm_st nabla)
           , ppr (nabla_ty_st nabla) ]

newtype Nablas = MkNablas (Bag Nabla)

initNablas :: Nablas
initNablas = MkNablas (unitBag initNabla)

instance Outputable Nablas where
  ppr (MkNablas nablas) = ppr nablas

instance Semigroup Nablas where
  MkNablas l <> MkNablas r = MkNablas (l `unionBags` r)

instance Monoid Nablas where
  mempty = MkNablas emptyBag

data TyState = TySt { ty_st_n :: !Int, ty_st_inert :: !InertTySet }

instance Outputable TyState where
  ppr (TySt n inert) = ppr n <+> ppr inert

initTyState :: TyState
initTyState = TySt 0 emptyInert

data TmState = TmSt
  { ts_facts :: !(UniqSDFM (Id Zk) VarInfo)
  , ts_reps :: !(CoreMap (Id Zk))
  , ts_dirty :: !(DIdSet Zk)
  }

data VarInfo = VI
  { vi_id :: !(Id Zk)
  , vi_pos :: ![PmAltConApp]
  , vi_neg :: !PmAltConSet
  , vi_bot :: BotInfo
  , vi_rcm :: !ResidualCompleteMatches
  }

data PmAltConApp = PACA
  { paca_con :: !PmAltCon
  , paca_tvs :: ![TyVar Zk]
  , paca_ids :: ![Id Zk]
  }

-- We may not EVER need BotInfo, since all types are unlifted and all fields strict
data BotInfo
  = IsBot
  | IsNotBot
  | MaybeBot
  deriving Eq

instance Outputable PmAltConApp where
  ppr PACA { paca_con = con, paca_tvs = tvs, paca_ids = ids }
    = hsep (ppr con : map (braces . ppr) tvs ++ map ppr ids)

instance Outputable BotInfo where
  ppr MaybeBot = underscore
  ppr IsBot = text "~⊥"
  ppr IsNotBot = text "≁⊥"

instance Outputable TmState where
  ppr (TmSt state reps dirty) = ppr state $$ ppr reps $$ ppr dirty

instance Outputable VarInfo where
  ppr (VI x pos neg bot cache)
    = braces (hcat (punctuate comma [ pp_x, pp_pos, pp_neg, ppr bot, pp_cache ]))
    where
      pp_x = ppr x <> colon <> (ppr $ varType x)
      pp_pos
        | [] <- pos = underscore
        | [p] <- pos = char '~' <> ppr p
        | otherwise = char '~' <> ppr pos
      pp_neg
        | isEmptyPmAltConSet neg = underscore
        | otherwise = char '≁' <> ppr neg
      pp_cache
        | RCM Nothing <- cache = underscore
        | otherwise = ppr cache

initTmState :: TmState
initTmState = TmSt emptyUSDFM emptyCoreMap emptyDVarSet

data ResidualCompleteMatches = RCM
  { rcm_vanilla :: !(Maybe DsCompleteMatch)
  }

getRcm :: ResidualCompleteMatches -> DsCompleteMatches
getRcm (RCM vanilla) = maybeToList vanilla

isRcmInitialized :: ResidualCompleteMatches -> Bool
isRcmInitialized (RCM vanilla) = isJust vanilla

instance Outputable ResidualCompleteMatches where
  ppr rcm = ppr (getRcm rcm)

emptyRCM :: ResidualCompleteMatches
emptyRCM = RCM Nothing

emptyVarInfo :: Id Zk -> VarInfo
emptyVarInfo x = VI
  { vi_id = x
  , vi_pos = []
  , vi_neg = emptyPmAltConSet
  , vi_bot = MaybeBot
  , vi_rcm = emptyRCM
  }

lookupVarInfo :: TmState -> Id Zk -> VarInfo
lookupVarInfo (TmSt env _ _) x = fromMaybe (emptyVarInfo x) (lookupUSDFM env x)

{-# INLINE tryVarInfo #-}
tryVarInfo :: Functor f => (VarInfo -> f (a, VarInfo)) -> Nabla -> Id Zk -> f (a, Nabla) 
tryVarInfo f nabla@MkNabla{ nabla_tm_st = ts@TmSt{ ts_facts = env } } x
  = set_vi <$> f (lookupVarInfo ts x)
  where
    set_vi (a, vi') =
      (a, nabla{ nabla_tm_st = ts{ ts_facts = addToUSDFM env (vi_id vi') vi' } })

data PmLit = PmLit
  { pm_lit_ty :: Type Zk
  , pm_lit_val :: PmLitValue
  }

data PmLitValue
  = PmLitOverInt Int Integer
  | PmLitOverRat Int FractionalLit
  | PmLitChar Char
  | PmLitOverString FastString

data PmEquality
  = Equal
  | Disjoint
  | PossiblyOverlap
  deriving (Eq, Show)

decEquality :: Bool -> PmEquality
decEquality True = Equal
decEquality False = Disjoint

eqPmLit :: PmLit -> PmLit -> PmEquality
eqPmLit (PmLit t1 v1) (PmLit t2 v2)
  | not (t1 `eqType` t2) = Disjoint
  | otherwise = go v1 v2
  where
    go (PmLitChar c1) (PmLitChar c2) = decEquality (c1 == c2)
    go (PmLitOverInt n1 i1) (PmLitOverInt n2 i2)
      | n1 == n2 && i1 == i2 = Equal
    go (PmLitOverRat n1 r1) (PmLitOverRat n2 r2)
      | n1 == n2 && r1 == r2 = Equal
    go (PmLitOverString s1) (PmLitOverString s2)
      | s1 == s2 = Equal
    go _ _ = PossiblyOverlap

eqConLike :: ConLike Zk -> ConLike Zk -> PmEquality
eqConLike (RealDataCon dc1) (RealDataCon dc2) = decEquality (dc1 == dc2)
eqConLike _ _ = panic "imposible"

data PmAltCon
  = PmAltConLike (ConLike Zk)
  | PmAltLit PmLit

data PmAltConSet = PACS !(UniqDSet (ConLike Zk)) ![PmLit]

emptyPmAltConSet :: PmAltConSet
emptyPmAltConSet = PACS emptyUniqDSet []

isEmptyPmAltConSet :: PmAltConSet -> Bool
isEmptyPmAltConSet (PACS cls lits) = isEmptyUniqDSet cls && null lits

pmAltConSetElems :: PmAltConSet -> [PmAltCon]
pmAltConSetElems (PACS cls lits) = map PmAltConLike (uniqDSetToList cls) ++ map PmAltLit lits

pprAltConSetElems :: PmAltConSet -> [PmAltCon]
pprAltConSetElems (PACS cls lits)
  = map PmAltConLike (uniqDSetToList cls) ++ map PmAltLit lits

instance Outputable PmAltConSet where
  ppr = ppr . pmAltConSetElems

eqPmAltCon :: PmAltCon -> PmAltCon -> PmEquality
eqPmAltCon (PmAltConLike cl1) (PmAltConLike cl2) = eqConLike cl1 cl2
eqPmAltCon (PmAltLit l1) (PmAltLit l2) = eqPmLit l1 l2
eqPmAltCon _ _ = PossiblyOverlap

instance Outputable PmLitValue where
  ppr (PmLitChar c) = pprCsChar c
  ppr (PmLitOverInt n i) = minuses n (ppr i)
  ppr (PmLitOverRat n r) = minuses n (ppr r)
  ppr (PmLitOverString s) = pprCsString s

minuses :: Int -> SDoc -> SDoc
minuses n sdoc = iterate (\sdoc -> parens (char '_' <> sdoc)) sdoc !! n

instance Outputable PmLit where
  ppr (PmLit ty v) = ppr v

instance Outputable PmAltCon where
  ppr (PmAltConLike cl) = ppr cl
  ppr (PmAltLit l) = ppr l
