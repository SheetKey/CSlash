{-# LANGUAGE RecordWildCards #-}
module CSlash.Core.Stats where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Types.Basic
import CSlash.Core as Core
import CSlash.Utils.Outputable
-- import CSlash.Core.Coercion
import CSlash.Types.Tickish
import CSlash.Types.Var
import CSlash.Core.Type(Type, TypeCoercion, typeSize)
import CSlash.Core.Kind
import CSlash.Types.Var.Id (isJoinId)

import CSlash.Utils.Panic

data CoreStats = CS
  { cs_tm :: !Int
  , cs_ty :: !Int
  , cs_ki :: !Int
  , cs_ty_co :: !Int
  , cs_ki_co :: !Int
  , cs_vb :: !Int
  , cs_jb :: !Int
  }

instance Outputable CoreStats where
  ppr CS {..} = braces $ sep [ text "terms:" <+> intWithCommas cs_tm <> comma
                             , text "types TODO:" <+> intWithCommas cs_ty <> comma
                             , text "kinds TODO:" <+> intWithCommas cs_ki <> comma
                             , text "type coercions TODO:" <+> intWithCommas cs_ty_co <> comma
                             , text "kind coercions TODO:" <+> intWithCommas cs_ki_co <> comma
                             , text "joins:" <+> intWithCommas cs_jb <> char '/' <>
                                                 intWithCommas (cs_vb + cs_jb)
                             ]

plusCS :: CoreStats -> CoreStats -> CoreStats
plusCS (CS p1 q1 k1 r1 s1 v1 j1) (CS p2 q2 k2 r2 s2 v2 j2)
  = CS (p1 + p2) (q1 + q2) (k1 + k2) (r1 + r2) (s1 + s2) (v1 + v2) (j1 + j2)

zeroCS :: CoreStats
zeroCS = CS 0 0 0 0 0 0 0

oneTM :: CoreStats
oneTM = zeroCS { cs_tm = 1 }

sumCS :: (a -> CoreStats) -> [a] -> CoreStats
sumCS f = foldl' (\s a -> plusCS s (f a)) zeroCS

coreBindsStats :: [CoreBind] -> CoreStats
coreBindsStats = sumCS (bindStats TopLevel)

bindStats :: TopLevelFlag -> CoreBind -> CoreStats
bindStats top_lvl (NonRec v r) = bindingStats top_lvl v r
bindStats top_lvl (Rec prs) = sumCS (\(v, r) -> bindingStats top_lvl v r) prs

bindingStats :: TopLevelFlag -> CoreId -> CoreExpr -> CoreStats
bindingStats top_lvl v r = letBndrStats top_lvl v `plusCS` exprStats r

letBndrStats :: TopLevelFlag -> CoreId -> CoreStats
letBndrStats top_lvl v
  | isTopLevel top_lvl = bndrStats (Core.Id v)
  | isJoinId v = oneTM { cs_jb = 1 } `plusCS` ty_stats
  | otherwise = oneTM { cs_vb = 1 } `plusCS` ty_stats
  where
    ty_stats = tyStats (varType v)

bndrStats :: CoreBndr -> CoreStats
bndrStats (Core.Id id) = oneTM `plusCS` tyStats (varType id)
bndrStats (Tv tv) = oneTM `plusCS` kiStats (varKind tv)
bndrStats (KCv kcv) = oneTM `plusCS` kiStats (varKind kcv)
bndrStats (Kv _) = oneTM

exprStats :: CoreExpr -> CoreStats
exprStats (Var {}) = oneTM
exprStats (Lit {}) = oneTM
exprStats (Type t) = tyStats t
exprStats (KiCo c) = kiCoStats c
exprStats (Kind k) = kiStats k
exprStats (App f a) = exprStats f `plusCS` exprStats a
exprStats (Lam b _ e) = bndrStats b `plusCS` exprStats e
exprStats (Let b e) = bindStats NotTopLevel b `plusCS` exprStats e
exprStats (Case e b _ as) = exprStats e `plusCS` bndrStats (Core.Id b) `plusCS` sumCS altStats as
exprStats (Cast e co) = tyCoStats co `plusCS` exprStats e
exprStats (Tick _ e) = exprStats e

altStats :: CoreAlt -> CoreStats
altStats (Alt _ bs r) = altBndrStats bs `plusCS` exprStats r

altBndrStats :: [CoreId] -> CoreStats
altBndrStats vs = oneTM `plusCS` sumCS (tyStats . varType) vs

tyStats :: CoreType -> CoreStats
tyStats ty = zeroCS { cs_ty = 0{-typeSize ty-} }

kiStats :: CoreMonoKind -> CoreStats
kiStats ki = zeroCS { cs_ki = 0 {-monoKindSize ki-} }

tyCoStats :: TypeCoercion Zk -> CoreStats
tyCoStats co = zeroCS { cs_ty_co = 0 {-tyCoercionSize co-} }

kiCoStats :: KindCoercion Zk -> CoreStats
kiCoStats co = zeroCS { cs_ki_co = 0 {-kiCoercionSize co-} }

