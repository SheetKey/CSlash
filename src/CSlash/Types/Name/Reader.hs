{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Types.Name.Reader where

import Prelude hiding ((<>))

import CSlash.Language.Syntax.Module.Name

import CSlash.Data.Bag
import CSlash.Data.FastString
import CSlash.Types.GREInfo
import CSlash.Types.SrcLoc
import CSlash.Types.Unique
import CSlash.Types.Name
import CSlash.Types.Name.Occurrence
import CSlash.Unit.Types
import CSlash.Utils.Outputable

import Control.DeepSeq
import Data.Data

data RdrName
  = Unqual OccName
  | Qual ModuleName OccName
  | Orig Module OccName
  | Exact Name
  deriving Data

unknownToVar :: RdrName -> RdrName
unknownToVar (Unqual (OccName UNKNOWN_NS fs)) = Unqual (OccName VarName fs)
unknownToVar (Qual mn (OccName UNKNOWN_NS fs)) = Qual mn (OccName VarName fs)
unknownToVar _ = error "unknownToVar"

unknownToTv :: RdrName -> RdrName
unknownToTv (Unqual (OccName UNKNOWN_NS fs)) = Unqual (OccName TvName fs)  
unknownToTv (Qual mn (OccName UNKNOWN_NS fs)) = Qual mn (OccName TvName fs)
unknownToTv _ = error "unknownToVar"

unknownToKv :: RdrName -> RdrName
unknownToKv (Unqual (OccName UNKNOWN_NS fs)) = Unqual (OccName KvName fs)  
unknownToKv (Qual mn (OccName UNKNOWN_NS fs)) = Qual mn (OccName KvName fs)
unknownToKv _ = error "unknownToVar"

unknownToData :: RdrName -> RdrName
unknownToData (Unqual (OccName UNKNOWN_NS fs)) = Unqual (OccName DataName fs)  
unknownToData (Qual mn (OccName UNKNOWN_NS fs)) = Qual mn (OccName DataName fs)
unknownToData _ = error "unknownToVar"

unknownToTcCls :: RdrName -> RdrName
unknownToTcCls (Unqual (OccName UNKNOWN_NS fs)) = Unqual (OccName TcClsName fs)  
unknownToTcCls (Qual mn (OccName UNKNOWN_NS fs)) = Qual mn (OccName TcClsName fs)
unknownToTcCls _ = error "unknownToVar"

instance HasOccName RdrName where
  occName = rdrNameOcc

rdrNameOcc :: RdrName -> OccName
rdrNameOcc (Qual _ occ) = occ
rdrNameOcc (Unqual occ) = occ
rdrNameOcc (Orig _ occ) = occ
rdrNameOcc (Exact name) = nameOccName name

rdrNameSpace :: RdrName -> NameSpace
rdrNameSpace = occNameSpace . rdrNameOcc

mkUnqual :: NameSpace -> FastString -> RdrName
mkUnqual sp n = Unqual (mkOccNameFS sp n)

nukeExact :: Name -> RdrName
nukeExact n
  | isExternalName n = Orig (nameModule n) (nameOccName n)
  | otherwise = Unqual (nameOccName n)

isExact_maybe :: RdrName -> Maybe Name
isExact_maybe (Exact n) = Just n
isExact_maybe _ = Nothing

instance Outputable RdrName where
  ppr (Exact name) = ppr name
  ppr (Unqual occ) = ppr occ
  ppr (Qual mod occ) = ppr mod <> dot <> ppr occ
  ppr (Orig mod occ) = getPprStyle (\sty -> pprModulePrefix sty mod occ <> ppr occ)

instance OutputableBndr RdrName where
  pprBndr _ n = ppr n

  pprInfixOcc rdr = pprInfixVar (isSymOcc (rdrNameOcc rdr)) (ppr rdr)
  pprPrefixOcc rdr
    | Just name <- isExact_maybe rdr = pprPrefixName name
    | otherwise = pprPrefixVar (isSymOcc (rdrNameOcc rdr)) (ppr rdr)

instance Eq RdrName where
  (Exact n1) == (Exact n2) = n1 == n2
  (Exact n1) == r2@(Orig _ _) = nukeExact n1 == r2
  r1@(Orig _ _) == (Exact n2) = r1 == nukeExact n2
  (Orig m1 o1) == (Orig m2 o2) = m1 == m2 && o1 == o2
  (Qual m1 o1) == (Qual m2 o2) = m1 == m2 && o1 == o2
  (Unqual o1) == (Unqual o2) = o1 == o2
  _ == _ = False

type GlobalRdrEnv = GlobalRdrEnvX GREInfo

type GlobalRdrEnvX info = OccEnv [GlobalRdrEltX info]

data GlobalRdrEltX info = GRE
  { gre_name :: !Name
  , gre_par :: !Parent
  , gre_lcl :: !Bool
  , gre_imp :: !(Bag ImportSpec)
  , gre_info :: info
  }
  deriving (Data)

data Parent
  = NoParent
  | ParentIs { par_is :: !Name }
  deriving (Eq, Data)

instance Outputable Parent where
  ppr NoParent = empty
  ppr (ParentIs n) = text "parent:" <> ppr n

instance NFData Parent where
  rnf NoParent = ()
  rnf (ParentIs n) = rnf n

data ImportSpec = ImpSpec
  { is_decl :: !ImpDeclSpec
  , is_item :: !ImpItemSpec
  }
  deriving (Eq, Data)

instance NFData ImportSpec where
  rnf = rwhnf

data ImpDeclSpec = ImpDeclSpec
  { is_mod :: !Module
  , is_as :: !ModuleName
  , is_qual :: !Bool
  , is_dloc :: !SrcSpan
  }
  deriving (Eq, Data)

data ImpItemSpec
  = ImpAll
  | ImpSome
    { is_explicit :: !Bool
    , is_iloc :: !SrcSpan
    }
  deriving (Eq, Data)

importSpecLoc :: ImportSpec -> SrcSpan
importSpecLoc (ImpSpec decl ImpAll) = is_dloc decl
importSpecLoc (ImpSpec _ item) = is_iloc item

importSpecModule :: ImportSpec -> ModuleName
importSpecModule = moduleName . is_mod . is_decl

instance Outputable ImportSpec where
  ppr imp_spec
    = text "imported" <+> qual
      <+> text "from" <+> quotes (ppr (importSpecModule imp_spec))
      <+> pprLoc (importSpecLoc imp_spec)
    where
      qual | is_qual (is_decl imp_spec) = text "qualified"
           | otherwise = empty

pprLoc :: SrcSpan -> SDoc
pprLoc (RealSrcSpan s _) = text "at" <+> ppr s
pprLoc (UnhelpfulSpan {}) = empty

opIsAt :: RdrName -> Bool
opIsAt e = e == mkUnqual varName (fsLit "@")
