{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module CSlash.Llvm.MetaData where

import Prelude hiding ((<>))

import CSlash.Llvm.Types
import CSlash.Utils.Outputable

newtype MetaId = MetaId Int
  deriving (Eq, Ord, Enum)

instance Outputable MetaId where
  ppr = ppMetaId

ppMetaId :: IsLine doc => MetaId -> doc
ppMetaId (MetaId n) = char '!' <> int n
{-# SPECIALIZE ppMetaId :: MetaId -> SDoc #-}
{-# SPECIALIZE ppMetaId :: MetaId -> HLine #-}

data MetaExpr
  = MetaStr !LMString
  | MetaLit !LlvmLit
  | MetaNode !MetaId
  | MetaVar !LlvmVar
  | MetaStruct [MetaExpr]
  deriving Eq

data MetaAnnot = MetaAnnot LMString MetaExpr
  deriving Eq

data MetaDecl
  = MetaNamed !LMString [MetaId]
  | MetaUnnamed !MetaId !MetaExpr

data ModuleFlagBehavior
  = MFBError
  | MFBWarning
  | MFBRequire
  | MFBOverride
  | MFBAppend
  | MFBAppendUnique
  | MFBMax
  | MFBMin

moduleFlagBehaviorToMetaExpr :: ModuleFlagBehavior -> MetaExpr
moduleFlagBehaviorToMetaExpr mfb = MetaLit $ LMIntLit n i32
  where
    n = case mfb of
      MFBError -> 1
      MFBWarning -> 2
      MFBRequire -> 3
      MFBOverride -> 4
      MFBAppend -> 5
      MFBAppendUnique -> 6
      MFBMax -> 7
      MFBMin -> 8

data ModuleFlag = ModuleFlag
  { mfBehavior :: ModuleFlagBehavior
  , mfName :: LMString
  , mfValue :: MetaExpr
  }

moduleFlagToMetaExpr :: ModuleFlag -> MetaExpr
moduleFlagToMetaExpr flag = MetaStruct
  [ moduleFlagBehaviorToMetaExpr (mfBehavior flag)
  , MetaStr (mfName flag)
  , mfValue flag
  ]
