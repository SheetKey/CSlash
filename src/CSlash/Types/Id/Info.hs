{-# LANGUAGE BinaryLiterals #-}

module CSlash.Types.Id.Info where

import Prelude hiding ((<>))

import CSlash.Core
import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Types.Name
import CSlash.Types.Basic
import CSlash.Core.DataCon
import CSlash.Unit.Module

import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Data.Data ( Data )
import Data.Word
import Data.Bits

data IdDetails tv kv
  = VanillaId
  | DataConId (DataCon tv kv)
  | TickBoxOpId TickBoxOp
  | JoinId JoinArity

instance Outputable (IdDetails tv kv) where
  ppr = pprIdDetails

pprIdDetails :: IdDetails tv kv -> SDoc
pprIdDetails VanillaId = empty
pprIdDetails other = brackets (pp other)
  where
    pp VanillaId = panic "pprIdDetails"
    pp (DataConId _) = text "DataCon"
    pp (TickBoxOpId _) = text "TickBoxOp"
    pp (JoinId arity) = text "JoinId" <> parens (int arity)

data IdInfo = IdInfo
  { realUnfoldingInfo :: Unfolding
  , occInfo :: OccInfo
  , bitfield :: {-# UNPACK #-} !BitField
  , lfInfo :: !(Maybe LambdaFormInfo)
  , tagSig :: !(Maybe TagSig)
  }

newtype BitField = BitField Word64

emptyBitField :: BitField
emptyBitField = BitField 0

bitfieldGetOneShotInfo :: BitField -> OneShotInfo
bitfieldGetOneShotInfo (BitField bits) =
  if testBit bits 0 then OneShotLam else NoOneShotInfo

bitfieldGetCafInfo :: BitField -> CafInfo
bitfieldGetCafInfo (BitField bits) =
  if testBit bits 1 then NoCafRefs else MayHaveCafRefs

bitfieldGetCallArityInfo :: BitField -> ArityInfo
bitfieldGetCallArityInfo (BitField bits) =
  fromIntegral (bits `shiftR` 3) .&. ((1 `shiftL` 30) - 1)

bitfieldGetArityInfo :: BitField -> ArityInfo
bitfieldGetArityInfo (BitField bits) =
  fromIntegral (bits `shiftR` 33)

bitfieldSetOneShotInfo :: OneShotInfo -> BitField -> BitField
bitfieldSetOneShotInfo info (BitField bits) =
  case info of
    NoOneShotInfo -> BitField (clearBit bits 0)
    OneShotLam -> BitField (setBit bits 0)

bitfieldSetCafInfo :: CafInfo -> BitField -> BitField
bitfieldSetCafInfo info (BitField bits) =
  case info of
    MayHaveCafRefs -> BitField (clearBit bits 1)
    NoCafRefs -> BitField (setBit bits 1)

bitfieldSetCallArityInfo :: ArityInfo -> BitField -> BitField
bitfieldSetCallArityInfo info bf@(BitField bits) =
  assert (info < 2^(30 :: Int) - 1) $
  bitfieldSetArityInfo (bitfieldGetArityInfo bf) $
  BitField ((fromIntegral info `shiftL` 3) .|. (bits .&. 0b111))

bitfieldSetArityInfo :: ArityInfo -> BitField -> BitField
bitfieldSetArityInfo info (BitField bits) =
  assert (info < 2^(30 :: Int) - 1) $
  BitField ((fromIntegral info `shiftL` 33) .|. (bits .&. ((1 `shiftL` 33) - 1)))

oneShotInfo :: IdInfo -> OneShotInfo
oneShotInfo = bitfieldGetOneShotInfo . bitfield

arityInfo :: IdInfo -> CafInfo
arityInfo = bitfieldGetCafInfo . bitfield

callArityInfo :: IdInfo -> ArityInfo
callArityInfo = bitfieldGetCallArityInfo . bitfield

tagSigInfo :: IdInfo -> Maybe TagSig
tagSigInfo = tagSig

setOccInfo :: IdInfo -> OccInfo -> IdInfo
setOccInfo info oc = oc `seq` info { occInfo = oc }

unfoldingInfo :: IdInfo -> Unfolding
unfoldingInfo info
  | isStrongLoopBreaker (occInfo info) = trimUnfolding $ realUnfoldingInfo info
  | otherwise = realUnfoldingInfo info

setUnfoldingInfo :: IdInfo -> Unfolding -> IdInfo
setUnfoldingInfo info uf = info { realUnfoldingInfo = uf }

setArityInfo :: IdInfo -> ArityInfo -> IdInfo
setArityInfo info ar = info { bitfield = bitfieldSetArityInfo ar (bitfield info) }

setCallArityInfo :: IdInfo -> ArityInfo -> IdInfo
setCallArityInfo info ar = info { bitfield = bitfieldSetCallArityInfo ar (bitfield info) }

setCafInfo :: IdInfo -> CafInfo -> IdInfo
setCafInfo info caf = info { bitfield = bitfieldSetCafInfo caf (bitfield info) }

setLFInfo :: IdInfo -> LambdaFormInfo -> IdInfo
setLFInfo info lf = info { lfInfo = Just lf }

setTagSig :: IdInfo -> TagSig -> IdInfo
setTagSig info sig = info { tagSig = Just sig }

setOneShotInfo :: IdInfo -> OneShotInfo -> IdInfo
setOneShotInfo info lb = info { bitfield = bitfieldSetOneShotInfo lb (bitfield info) }

vanillaIdInfo :: IdInfo
vanillaIdInfo
  = IdInfo { realUnfoldingInfo = noUnfolding
           , occInfo = noOccInfo
           , bitfield = bitfieldSetCafInfo vanillaCafInfo $
                        bitfieldSetArityInfo unknownArity $
                        bitfieldSetCallArityInfo unknownArity $
                        bitfieldSetOneShotInfo NoOneShotInfo $
                        emptyBitField
           , lfInfo = Nothing
           , tagSig = Nothing
           }
    
noCafIdInfo :: IdInfo
noCafIdInfo = vanillaIdInfo `setCafInfo` NoCafRefs

{- ********************************************************************
*                                                                      *
            Arity info about an Id
*                                                                      *
*********************************************************************-}

type ArityInfo = Arity

unknownArity :: Arity
unknownArity = 0

ppArityInfo :: Int -> SDoc
ppArityInfo 0 = empty
ppArityInfo n = hsep [text "Arity", int n]

{- *********************************************************************
*                                                                      *
           Code generator-related information
*                                                                      *
********************************************************************* -}

data CafInfo
  = MayHaveCafRefs
  | NoCafRefs
  deriving (Eq, Ord)

vanillaCafInfo :: CafInfo
vanillaCafInfo = MayHaveCafRefs

mayHaveCafRefs :: CafInfo -> Bool
mayHaveCafRefs MayHaveCafRefs = True
mayHaveCafRefs _ = False

instance Outputable CafInfo where
  ppr = ppCafInfo

ppCafInfo :: CafInfo -> SDoc
ppCafInfo NoCafRefs = text "NoCafRefs"
ppCafInfo MayHaveCafRefs = empty

{- *********************************************************************
*                                                                      *
            Bulk operations on IdInfo
*                                                                      *
********************************************************************* -}

trimUnfolding :: Unfolding -> Unfolding
trimUnfolding unf | isEvaldUnfolding unf = evaldUnfolding
                  | otherwise = noUnfolding

{- *********************************************************************
*                                                                      *
            TickBoxOp
*                                                                      *
********************************************************************* -}

type TickBoxId = Int

data TickBoxOp = TickBox Module {-# UNPACK #-} !TickBoxId

instance Outputable TickBoxOp where
  ppr (TickBox mod n) = text "tick" <+> ppr (mod, n)

{- *********************************************************************
*                                                                      *
            LambdaForInfo (moved from GHC.StgToCmm.Types)
*                                                                      *
********************************************************************* -}

data LambdaFormInfo
  = LFReEntrant
    !TopLevelFlag
    !RepArity
    !Bool
    !ArgDescr
  | LFCon
    !(DataCon (TyVar KiVar) KiVar)
  | LFUnknown
    !Bool

-- THIS SHOULD MOVE:
-- originally in GHC.Runtime.Heap.Layout
data ArgDescr
  = ArgUnknown

{- *********************************************************************
*                                                                      *
            TagSig (moved from GHC.Stg.InferTags.TagSig
*                                                                      *
********************************************************************* -}

newtype TagSig = TagSig TagInfo
  deriving (Eq)

data TagInfo
  = TagDunno
  | TagTuple [TagInfo]
  deriving (Eq)
