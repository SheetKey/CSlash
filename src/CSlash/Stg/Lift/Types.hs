module CSlash.Stg.Lift.Types where

import CSlash.Core (CoreId)
import CSlash.Core.Ppr ()
import CSlash.Types.Var.Id
import CSlash.Types.Demand
import CSlash.Types.Var.Set

import CSlash.Utils.Outputable

data Skeleton
  = ClosureSk !CoreId !DCoreIdSet !Skeleton
  | RhsSk !Card !Skeleton
  | AltSk !Skeleton !Skeleton
  | BothSk !Skeleton !Skeleton
  | NilSk

bothSk :: Skeleton -> Skeleton -> Skeleton
bothSk NilSk b = b
bothSk a NilSk = a
bothSk a b = BothSk a b

altSk :: Skeleton -> Skeleton -> Skeleton
altSk NilSk b = b
altSk a NilSk = a
altSk a b = AltSk a b

rhsSk :: Card -> Skeleton -> Skeleton
rhsSk _ NilSk = NilSk
rhsSk body_dmd skel = RhsSk body_dmd skel

data BinderInfo
  = BindsClosure !CoreId !Bool
  | BoringBinder !CoreId

binderInfoBndr :: BinderInfo -> CoreId
binderInfoBndr (BoringBinder bndr) = bndr
binderInfoBndr (BindsClosure bndr _) = bndr

binderInfoOccursAsArg :: BinderInfo -> Maybe Bool
binderInfoOccursAsArg BoringBinder{} = Nothing
binderInfoOccursAsArg (BindsClosure _ b) = Just b

instance Outputable Skeleton where
  ppr NilSk = text ""
  ppr (AltSk l r) = vcat
    [ text "{ " <+> ppr l
    , text "ALT"
    , text "  " <+> ppr r
    , text "}"
    ]
  ppr (BothSk l r) = ppr l $$ ppr r
  ppr (ClosureSk f fvs body) = ppr f <+> ppr fvs $$ nest 2 (ppr body)
  ppr (RhsSk card body) = hcat
    [ lambda
    , ppr card
    , dot
    , ppr body
    ]

instance Outputable BinderInfo where
  ppr = ppr . binderInfoBndr

instance OutputableBndr BinderInfo where
  pprBndr b = pprBndr b . binderInfoBndr
  pprPrefixOcc = pprPrefixOcc . binderInfoBndr
  pprInfixOcc = pprInfixOcc . binderInfoBndr
  bndrIsJoin_maybe = bndrIsJoin_maybe . binderInfoBndr
