module CSlash.Language.Syntax.Decls where

import CSlash.Language.Syntax.Extension
import CSlash.Language.Syntax.Binds

import qualified Data.List

type LCsDecl p = XRec p (CsDecl p)

data CsDecl p
  = ValD (XValD p) (CsBind p)
  | SigD (XSigD p) (Sig p)

data CsGroup p = CsGroup
  { cs_ext :: XCCsGroup p
  , cs_valds :: CsValBinds p
  , cs_typeds :: [TypeGroup p]
  , cs_fixds :: [LFixitySig p]
  }

data TypeGroup p = TypeGroup
  { group_ext :: XCTypeGroup p
  , group_typeds :: [LCsBind p]
  , group_kisigs :: [LSig p]
  }

typeGroupTypeDecls :: [TypeGroup p] -> [LCsBind p]
typeGroupTypeDecls = Data.List.concatMap group_typeds

typeGroupKindSigs :: [TypeGroup p] -> [LSig p]
typeGroupKindSigs = Data.List.concatMap group_kisigs
