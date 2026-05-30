module CSlash.Llvm.Types where

import Prelude hiding ((<>))

import Data.Char
import Numeric

import CSlash.Platform
import CSlash.Data.FastString
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Types.Unique

import GHC.Float

-- Could move files
import qualified Data.Array.Unsafe as U ( castSTUArray )
import Data.Array.ST

import Control.Monad.ST
import Data.Word

doubleToBytes :: Double -> [Word8]
doubleToBytes d = runST $ do
  arr <- newArray_ ((0::Int), 7)
  writeArray arr 0 d
  let cast :: STUArray s Int Double -> ST s (STUArray s Int Word8)
      cast = U.castSTUArray
  arr <- cast arr
  i0 <- readArray arr 0
  i1 <- readArray arr 1
  i2 <- readArray arr 2
  i3 <- readArray arr 3
  i4 <- readArray arr 4
  i5 <- readArray arr 5
  i6 <- readArray arr 6
  i7 <- readArray arr 7
  return [i0,i1,i2,i3,i4,i5,i6,i7]
-- End could move

data LMGlobal = LMGlobal
  { getGlobalVar :: LlvmVar
  , getGlobalValue :: Maybe LlvmStatic
  }

type LMString = FastString

type LlvmAlias = (LMString, LlvmType)

data LlvmType
  = LMInt Int
  | LMFloat
  | LMDouble
  | LMPointer LlvmType
  | LMArray Int LlvmType
  | LMLabel
  | LMVoid
  | LMStructP [LlvmType]
  | LMStructU [LlvmType]
  | LMAlias LlvmAlias
  | LMMetadata
  | LMFunction LlvmFunctionDecl
  deriving Eq

instance Outputable LlvmType where
  ppr = ppLlvmType

ppLlvmType :: IsLine doc => LlvmType -> doc
ppLlvmType t = case t of
  LMInt size -> char 'i' <> int size
  LMFloat -> text "float"
  LMDouble -> text "double"
  LMPointer x -> ppLlvmType x <> char '*'
  LMArray nr tp -> char '[' <> int nr <> text " x " <> ppLlvmType tp <> char ']'
  LMLabel -> text "label"
  LMVoid -> text "void"
  LMStructP tys -> text "<{" <> ppCommaJoin ppLlvmType tys <> text "}>"
  LMStructU tys -> text "{" <> ppCommaJoin ppLlvmType tys <> text "}"
  LMMetadata -> text "metadata"
  LMAlias (s, _) -> char '%' <> ftext s
  LMFunction (LlvmFunctionDecl _ _ _ r p _)
    -> ppLlvmType r <+> lparen <> ppParams p <> rparen
{-# SPECIALIZE ppLlvmType :: LlvmType -> SDoc #-}
{-# SPECIALIZE ppLlvmType :: LlvmType -> HLine #-}

ppLlvmTypeShort :: LlvmType -> String
ppLlvmTypeShort t = case t of
  LMInt size -> 'i' : show size
  LMFloat -> "f32"
  LMDouble -> "f64"
  _ -> pprPanic "ppLlvmTypeShort" (ppLlvmType t)

ppParams :: IsLine doc => [LlvmParameter] -> doc
ppParams p = ppCommaJoin ppLlvmType (fst <$> p)
{-# SPECIALIZE ppParams :: [LlvmParameter] -> SDoc #-}
{-# SPECIALIZE ppParams :: [LlvmParameter] -> HLine #-}

type LMSection = Maybe LMString
type LMAlign = Maybe Int

data LMConst
  = Global
  | Constant
  | Alias
  deriving Eq

data LlvmVar
  = LMGlobalVar LMString LlvmType LlvmLinkageType LMSection LMAlign LMConst
  | LMLocalVar Unique LlvmType
  | LMNLocalVar LMString LlvmType
  | LMLitVar LlvmLit
  deriving Eq

data LlvmLit
  = LMIntLit Integer LlvmType
  | LMFloatLit Double LlvmType
  | LMNullLit LlvmType
  deriving Eq

data LlvmStatic
  = LMComment LMString
  | LMStaticLit LlvmLit
  | LMUninitType LlvmType
  | LMStaticStr LMString LlvmType
  | LMStaticArray [LlvmStatic] LlvmType
  | LMStaticStructP [LlvmStatic] LlvmType
  | LMStaticStructU [LlvmStatic] LlvmType
  | LMStaticPointer LlvmVar
  -- Static expressions
  | LMTrunc LlvmStatic LlvmType
  | LMBitc LlvmStatic LlvmType
  | LMPtoI LlvmStatic LlvmType
  | LMAdd LlvmStatic LlvmStatic
  | LMSub LlvmStatic LlvmStatic

getVarType :: LlvmVar -> LlvmType
getVarType (LMGlobalVar _ y _ _ _ _) = y
getVarType (LMLocalVar _ y) = y
getVarType (LMNLocalVar _ y) = y
getVarType (LMLitVar l) = getLitType l

getLitType :: LlvmLit -> LlvmType
getLitType (LMIntLit _ t) = t
getLitType (LMFloatLit _ t) = t
getLitType (LMNullLit t) = t

getStatType :: LlvmStatic -> LlvmType
getStatType (LMStaticLit l) = getLitType l
getStatType (LMUninitType t) = t
getStatType (LMStaticStr _ t) = t
getStatType (LMStaticArray _ t) = t
getStatType (LMStaticStructP _ t) = t
getStatType (LMStaticStructU _ t) = t
getStatType (LMStaticPointer v) = getVarType v
getStatType (LMTrunc _ t) = t
getStatType (LMBitc _ t) = t
getStatType (LMPtoI _ t) = t
getStatType (LMAdd t _) = getStatType t
getStatType (LMSub t _) = getStatType t
getStatType (LMComment _) = error "Can't call getStatType on LMComment!"

getLink :: LlvmVar -> LlvmLinkageType
getLink (LMGlobalVar _ _ l _ _ _) = l
getLink _ = Internal

pLift :: LlvmType -> LlvmType
pLift LMLabel = error "Labels are unliftable"
pLift LMVoid = error "Voids are unliftable"
pLift LMMetadata = error "Metadatas are unliftable"
pLift x = LMPointer x

pVarLift :: LlvmVar -> LlvmVar
pVarLift (LMGlobalVar s t l x a c) = LMGlobalVar s (pLift t) l x a c
pVarLift (LMLocalVar s t) = LMLocalVar s (pLift t)
pVarLift (LMNLocalVar s t) = LMNLocalVar s (pLift t)
pVarLift (LMLitVar _) = error "Can't lift a literal type!"

pLower :: LlvmType -> LlvmType
pLower (LMPointer x) = x
pLower x = pprPanic "llvmGen(pLower)" $
           ppr x <+> text " is an unlowerable type, need a pointer"

pVarLower :: LlvmVar -> LlvmVar
pVarLower (LMGlobalVar s t l x a c) = LMGlobalVar s (pLower t) l x a c
pVarLower (LMLocalVar s t) = LMLocalVar s (pLower t)
pVarLower (LMNLocalVar s t) = LMNLocalVar s (pLower t)
pVarLower (LMLitVar _) = error "Can't lower a literal type!"

isInt :: LlvmType -> Bool
isInt (LMInt _) = True
isInt _ = False

isFloat :: LlvmType -> Bool
isFloat LMFloat = True
isFloat LMDouble = True
isFloat _ = False

isPointer :: LlvmType -> Bool
isPointer (LMPointer _) = True
isPointer _ = False

isGlobal :: LlvmVar -> Bool
isGlobal LMGlobalVar{} = True
isGlobal _ = False

llvmWidthInBits :: Platform -> LlvmType -> Int
llvmWidthInBits platform t = case t of
  LMInt n -> n
  LMFloat -> 32
  LMDouble -> 64
  LMPointer _ -> llvmWidthInBits platform (llvmWord platform)
  LMArray n t -> n * llvmWidthInBits platform t
  LMLabel -> 0
  LMVoid -> 0
  LMStructP tys -> sum $ map (llvmWidthInBits platform) tys
  LMStructU _ -> panic "llvmWidthInBits: not implemented for LMSturctU"
  LMFunction _ -> 0
  LMAlias (_, t) -> llvmWidthInBits platform t
  LMMetadata -> panic "llvmWidthInBits: Meta-data has no runtime representation!"

i64 :: LlvmType 
i64 = LMInt 64

i32 :: LlvmType
i32 = LMInt 32
 
i16 :: LlvmType
i16 = LMInt 16

i8 :: LlvmType
i8 = LMInt 8

i1 :: LlvmType
i1 = LMInt 1

i8Ptr :: LlvmType
i8Ptr = pLift i8
                  
llvmWord :: Platform -> LlvmType          
llvmWord platform = LMInt (platformWordSizeInBytes platform * 8)
 
llvmWordPtr :: Platform -> LlvmType
llvmWordPtr platform = pLift (llvmWord platform)

data LlvmFunctionDecl = LlvmFunctionDecl
  { decName :: LMString
  , funcLinkage :: LlvmLinkageType
  , funcCc :: LlvmCallConvention
  , decReturnType :: LlvmType
  , decParams :: [LlvmParameter]
  , funcAlign :: LMAlign
  }
  deriving Eq

type LlvmFunctionDecls = [LlvmFunctionDecl]

type LlvmParameter = (LlvmType, [LlvmParamAttr])

data LlvmParamAttr
  = ZeroExt
  | SignExt
  | InReg
  | ByVal
  | SRet
  | NoAlias
  | NoCapture
  | Nest
  deriving Eq

instance Outputable LlvmParamAttr where
  ppr = ppLlvmParamAttr

ppLlvmParamAttr :: IsLine doc => LlvmParamAttr -> doc
ppLlvmParamAttr ZeroExt = text "zeroext"
ppLlvmParamAttr SignExt = text "signext"
ppLlvmParamAttr InReg = text "inreg"
ppLlvmParamAttr ByVal = text "byval"
ppLlvmParamAttr SRet = text "sret"
ppLlvmParamAttr NoAlias = text "noalias"
ppLlvmParamAttr NoCapture = text "nocapture"
ppLlvmParamAttr Nest = text "nest"
{-# SPECIALIZE ppLlvmParamAttr :: LlvmParamAttr -> SDoc #-}
{-# SPECIALIZE ppLlvmParamAttr :: LlvmParamAttr -> HLine #-}

data LlvmFuncAttr
  = AlwaysInline
  | InlineHint
  | NoInline
  | OptSize
  | NoReturn
  | NoUnwind
  | ReadNone
  | ReadOnly
  | NoImplicitFloat
  deriving Eq

instance Outputable LlvmFuncAttr where
  ppr = ppLlvmFuncAttr

ppLlvmFuncAttr :: IsLine doc => LlvmFuncAttr -> doc
ppLlvmFuncAttr AlwaysInline = text "alwaysinline"
ppLlvmFuncAttr InlineHint = text "inlinehint"
ppLlvmFuncAttr NoInline = text "noinline"
ppLlvmFuncAttr OptSize = text "optsize"
ppLlvmFuncAttr NoReturn = text "noreturn"
ppLlvmFuncAttr NoUnwind = text "nounwind"
ppLlvmFuncAttr ReadNone = text "readnone"
ppLlvmFuncAttr ReadOnly = text "readonly"
ppLlvmFuncAttr NoImplicitFloat = text "noimplicitfloat"
{-# SPECIALIZE ppLlvmFuncAttr :: LlvmFuncAttr -> SDoc #-}
{-# SPECIALIZE ppLlvmFuncAttr :: LlvmFuncAttr -> HLine #-}

data LlvmCallType
  = StdCall
  | TailCall
  deriving (Eq, Show)

data LlvmCallConvention
  = CC_Ccc
  | CC_Fastcc
  | CC_Coldcc
  deriving Eq

instance Outputable LlvmCallConvention where
  ppr = ppLlvmCallConvention

ppLlvmCallConvention :: IsLine doc => LlvmCallConvention -> doc
ppLlvmCallConvention CC_Ccc = text "ccc"
ppLlvmCallConvention CC_Fastcc = text "fastcc"
ppLlvmCallConvention CC_Coldcc = text "coldcc"
{-# SPECIALIZE ppLlvmCallConvention :: LlvmCallConvention -> SDoc #-}
{-# SPECIALIZE ppLlvmCallConvention :: LlvmCallConvention -> HLine #-}

data LlvmLinkageType
  = Internal
  | LinkOnce
  | Weak
  | Appending
  | ExternWeak
  | ExternallyVisible
  | External
  | Private
  deriving Eq

instance Outputable LlvmLinkageType where
  ppr = ppLlvmLinkageType

ppLlvmLinkageType :: IsLine doc => LlvmLinkageType -> doc
ppLlvmLinkageType Internal = text "internal"
ppLlvmLinkageType LinkOnce = text "linkonce"
ppLlvmLinkageType Weak = text "weak"
ppLlvmLinkageType Appending = text "appending"
ppLlvmLinkageType ExternWeak = text "extern_weak"
ppLlvmLinkageType ExternallyVisible = empty
ppLlvmLinkageType External = text "external"
ppLlvmLinkageType Private = text "private"
{-# SPECIALIZE ppLlvmLinkageType :: LlvmLinkageType -> SDoc #-}
{-# SPECIALIZE ppLlvmLinkageType :: LlvmLinkageType -> HLine #-}

data LlvmMachOp
  = LM_MO_Add
  | LM_MO_Sub
  | LM_MO_Mul
  | LM_MO_UDiv
  | LM_MO_SDiv
  | LM_MO_URem
  | LM_MO_SRem

  | LM_MO_FAdd
  | LM_MO_FSub
  | LM_MO_FMul
  | LM_MO_FDiv
  | LM_MO_FRem

  | LM_MO_Shl
  | LM_MO_LShr
  | LM_MO_AShr

  | LM_MO_And
  | LM_MO_Or
  | LM_MO_Xor
  deriving Eq

instance Outputable LlvmMachOp where
  ppr = ppLlvmMachOp

ppLlvmMachOp :: IsLine doc => LlvmMachOp -> doc
ppLlvmMachOp LM_MO_Add  = text "add"
ppLlvmMachOp LM_MO_Sub  = text "sub"
ppLlvmMachOp LM_MO_Mul  = text "mul"
ppLlvmMachOp LM_MO_UDiv = text "udiv"
ppLlvmMachOp LM_MO_SDiv = text "sdiv"
ppLlvmMachOp LM_MO_URem = text "urem"
ppLlvmMachOp LM_MO_SRem = text "srem"
ppLlvmMachOp LM_MO_FAdd = text "fadd"
ppLlvmMachOp LM_MO_FSub = text "fsub"
ppLlvmMachOp LM_MO_FMul = text "fmul"
ppLlvmMachOp LM_MO_FDiv = text "fdiv"
ppLlvmMachOp LM_MO_FRem = text "frem"
ppLlvmMachOp LM_MO_Shl  = text "shl"
ppLlvmMachOp LM_MO_LShr = text "lshr"
ppLlvmMachOp LM_MO_AShr = text "ashr"
ppLlvmMachOp LM_MO_And  = text "and"
ppLlvmMachOp LM_MO_Or   = text "or"
ppLlvmMachOp LM_MO_Xor  = text "xor"
{-# SPECIALIZE ppLlvmMachOp :: LlvmMachOp -> SDoc #-}
{-# SPECIALIZE ppLlvmMachOp :: LlvmMachOp -> HLine #-} 

data LlvmCmpOp
  = LM_CMP_Eq
  | LM_CMP_Ne
  | LM_CMP_Ugt
  | LM_CMP_Uge
  | LM_CMP_Ult
  | LM_CMP_Ule
  | LM_CMP_Sgt
  | LM_CMP_Sge
  | LM_CMP_Slt
  | LM_CMP_Sle

  | LM_CMP_Feq
  | LM_CMP_Fne
  | LM_CMP_Fgt
  | LM_CMP_Fge
  | LM_CMP_Flt
  | LM_CMP_Fle
  deriving Eq

instance Outputable LlvmCmpOp where
  ppr = ppLlvmCmpOp

ppLlvmCmpOp :: IsLine doc => LlvmCmpOp -> doc
ppLlvmCmpOp LM_CMP_Eq  = text "eq"
ppLlvmCmpOp LM_CMP_Ne  = text "ne"
ppLlvmCmpOp LM_CMP_Ugt = text "ugt"
ppLlvmCmpOp LM_CMP_Uge = text "uge"
ppLlvmCmpOp LM_CMP_Ult = text "ult"
ppLlvmCmpOp LM_CMP_Ule = text "ule"
ppLlvmCmpOp LM_CMP_Sgt = text "sgt"
ppLlvmCmpOp LM_CMP_Sge = text "sge"
ppLlvmCmpOp LM_CMP_Slt = text "slt"
ppLlvmCmpOp LM_CMP_Sle = text "sle"
ppLlvmCmpOp LM_CMP_Feq = text "oeq"
ppLlvmCmpOp LM_CMP_Fne = text "une"
ppLlvmCmpOp LM_CMP_Fgt = text "ogt"
ppLlvmCmpOp LM_CMP_Fge = text "oge"
ppLlvmCmpOp LM_CMP_Flt = text "olt"
ppLlvmCmpOp LM_CMP_Fle = text "ole"
{-# SPECIALIZE ppLlvmCmpOp :: LlvmCmpOp -> SDoc #-}
{-# SPECIALIZE ppLlvmCmpOp :: LlvmCmpOp -> HLine #-}

data LlvmCastOp
  = LM_Trunc
  | LM_Zext 
  | LM_Sext 
  | LM_Fptrunc
  | LM_Fpext  
  | LM_Fptoui 
  | LM_Fptosi 
  | LM_Uitofp 
  | LM_Sitofp 
  | LM_Ptrtoint
  | LM_Inttoptr
  | LM_Bitcast 
  deriving Eq

instance Outputable LlvmCastOp where
  ppr = ppLlvmCastOp

ppLlvmCastOp :: IsLine doc => LlvmCastOp -> doc
ppLlvmCastOp LM_Trunc    = text "trunc"
ppLlvmCastOp LM_Zext     = text "zext"
ppLlvmCastOp LM_Sext     = text "sext"
ppLlvmCastOp LM_Fptrunc  = text "fptrunc"
ppLlvmCastOp LM_Fpext    = text "fpext"
ppLlvmCastOp LM_Fptoui   = text "fptoui"
ppLlvmCastOp LM_Fptosi   = text "fptosi"
ppLlvmCastOp LM_Uitofp   = text "uitofp"
ppLlvmCastOp LM_Sitofp   = text "sitofp"
ppLlvmCastOp LM_Ptrtoint = text "ptrtoint"
ppLlvmCastOp LM_Inttoptr = text "inttoptr"
ppLlvmCastOp LM_Bitcast  = text "bitcast"
{-# SPECIALIZE ppLlvmCastOp :: LlvmCastOp -> SDoc #-}
{-# SPECIALIZE ppLlvmCastOp :: LlvmCastOp -> HLine #-}

ppDouble :: IsLine doc => Platform -> Double -> doc
ppDouble platform d
  = let bs = doubleToBytes d
        hex d' = case showHex d' "" of
                   [] -> error "ppDouble: too few hex digits for float"
                   [x] -> ['0', x]
                   [x, y] -> [x, y]
                   _ -> error "ppDouble: too many hex digits for float"
        fixEndian = case platformByteOrder platform of
          BigEndian -> id
          LittleEndian -> reverse
        str = map toUpper $ concat $ fixEndian $ map hex bs
    in text "0x" <> text str
{-# SPECIALIZE ppDouble :: Platform -> Double -> SDoc #-}
{-# SPECIALIZE ppDouble :: Platform -> Double -> HLine #-}

narrowFp :: Double -> Float
{-# NOINLINE narrowFp #-}
narrowFp = double2Float

widenFp :: Float -> Double
{-# NOINLINE widenFp #-}
widenFp = float2Double

ppFloat :: IsLine doc => Platform -> Float -> doc
ppFloat platform = ppDouble platform . widenFp
{-# SPECIALIZE ppFloat :: Platform -> Float -> SDoc #-}
{-# SPECIALIZE ppFloat :: Platform -> Float -> HLine #-}

ppCommaJoin :: IsLine doc => (a -> doc) -> [a] -> doc
ppCommaJoin ppr strs = hsep $ punctuate comma (map ppr strs)
{-# SPECIALIZE ppFloat :: Platform -> Float -> SDoc #-}
{-# SPECIALIZE ppFloat :: Platform -> Float -> HLine #-}

ppSpaceJoin :: IsLine doc => (a -> doc) -> [a] -> doc
ppSpaceJoin ppr strs = hsep (map ppr strs)
{-# SPECIALIZE ppSpaceJoin :: (a -> SDoc) -> [a] -> SDoc #-}
{-# SPECIALIZE ppSpaceJoin :: (a -> HLine) -> [a] -> HLine #-}
