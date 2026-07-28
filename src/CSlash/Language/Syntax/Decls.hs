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
  , cs_tykids :: [TyKiGroup p]
  , cs_fixds :: [LFixitySig p]
  }

data TyKiGroup p = TyKiGroup
  { group_ext :: XCTypeGroup p
  , group_typeds :: [LCsBind p]
  , group_kindds :: [LCsBind p]
  , group_kisigs :: [LSig p]
  }

tykiGroupTypeDecls :: [TyKiGroup p] -> [LCsBind p]
tykiGroupTypeDecls = Data.List.concatMap group_typeds

tykiGroupKindDecls :: [TyKiGroup p] -> [LCsBind p]
tykiGroupKindDecls = Data.List.concatMap group_kindds

tykiGroupKindSigs :: [TyKiGroup p] -> [LSig p]
tykiGroupKindSigs = Data.List.concatMap group_kisigs
