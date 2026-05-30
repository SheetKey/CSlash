module CSlash.Llvm.Syntax where

import CSlash.Llvm.MetaData
import CSlash.Llvm.Types

import CSlash.Types.Unique

type LlvmBlockId = Unique

data LlvmBlock = LlvmBlock
  { blockLabel :: LlvmBlockId
  , blockStmts :: [LlvmStatement]
  }

type LlvmBlocks = [LlvmBlock]

data LlvmModule = LlvmModule
  { modComments :: [LMString]
  , modAliases :: [LlvmAlias]
  , modMeta :: [MetaDecl]
  , modGlobals :: [LMGlobal]
  , modFwdDecls :: LlvmFunctionDecls
  , modFuncs :: LlvmFunctions
  }

data LlvmFunction = LlvmFunction
  { funcDecl :: LlvmFunctionDecl
  , funcArgs :: [LMString]
  , funcAttrs :: [LlvmFuncAttr]
  , funcSect :: LMSection
  , funcPrefix :: Maybe LlvmStatic
  , funcBody :: LlvmBlocks
  }

type LlvmFunctions = [LlvmFunction]

type SingleThreaded = Bool

data LlvmSyncOrdering
  = SyncUnord
  | SyncMonotonic
  | SyncAcquire
  | SyncRelease
  | SyncAcqRel
  | SyncSeqCst
  deriving (Show, Eq)

data LlvmAtomicOp
  = LAO_Xchg
  | LAO_Add
  | LAO_Sub
  | LAO_And
  | LAO_Nand
  | LAO_Or
  | LAO_Xor
  | LAO_Max
  | LAO_Min
  | LAO_Umax
  | LAO_Umin
  deriving (Show, Eq)

data LlvmStatement
  = Assignment LlvmVar LlvmExpression
  | Fence Bool LlvmSyncOrdering
  | Branch LlvmVar
  | BranchIf LlvmVar LlvmVar LlvmVar
  | Comment [LMString]
  | MkLabel LlvmBlockId
  | Store LlvmVar LlvmVar LMAlign [MetaAnnot]
  | Switch LlvmVar LlvmVar [(LlvmVar, LlvmVar)]
  | Return (Maybe LlvmVar)
  | Unreachable
  | Expr LlvmExpression
  | Nop
  deriving Eq

data LlvmExpression
  = Alloca LlvmType Int
  | LlvmOp LlvmMachOp LlvmVar LlvmVar
  | Compare LlvmCmpOp LlvmVar LlvmVar
  | ExtractV LlvmVar Int
  | Insert LlvmVar LlvmVar LlvmVar
  | Load LlvmVar LMAlign
  | ALoad LlvmSyncOrdering SingleThreaded LlvmVar
  | GetElemPtr Bool LlvmVar [LlvmVar]
  | Cast LlvmCastOp LlvmVar LlvmType
  | AtomicRMW LlvmAtomicOp LlvmVar LlvmVar LlvmSyncOrdering
  | CmpXChg LlvmVar LlvmVar LlvmVar LlvmSyncOrdering LlvmSyncOrdering
  | Call LlvmCallType LlvmVar [LlvmVar] [LlvmFuncAttr]
  | CallM LlvmCallType LlvmVar [MetaExpr] [LlvmFuncAttr]
  | Phi LlvmType [(LlvmVar, LlvmVar)]
  | Asm LMString LMString LlvmType [LlvmVar] Bool Bool
  | MExpr [MetaAnnot] LlvmExpression
  deriving Eq
