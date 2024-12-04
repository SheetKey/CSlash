{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module CSlash.Cs.Decls
  ( module CSlash.Language.Syntax.Decls
  , module CSlash.Cs.Decls
  ) where

import CSlash.Language.Syntax.Decls

import CSlash.Cs.Binds
import CSlash.Cs.Type
import CSlash.Types.Basic
import CSlash.Language.Syntax.Extension
import CSlash.Cs.Extension
import CSlash.Parser.Annotation
import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.Fixity

-- others:
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Types.SrcLoc
import CSlash.Types.SourceText
import CSlash.Core.Type

import CSlash.Data.Bag
import CSlash.Data.Maybe
import Data.Data (Data)

type instance XValD (CsPass _) = NoExtField
type instance XSigD (CsPass _) = NoExtField

partitionBindsAndSigs :: [LCsDecl Ps] -> (LCsBinds Ps, [LSig Ps])
partitionBindsAndSigs [] = (emptyBag, [])
partitionBindsAndSigs ((L l decl) : ds) =
  let (bs, ss) = partitionBindsAndSigs ds in
    case decl of
      ValD _ b -> (L l b `consBag` bs, ss)
      SigD _ s -> (bs, L l s : ss)

appendGroups :: CsGroup (CsPass p) -> CsGroup (CsPass p) -> CsGroup (CsPass p)
appendGroups
  CsGroup { cs_valds = val_groups1
          , cs_typeds = typeds1
          , cs_fixds = fixds1 }
  CsGroup { cs_valds = val_groups2
          , cs_typeds = typeds2
          , cs_fixds = fixds2 }
  = CsGroup { cs_ext = noExtField
            , cs_valds = val_groups1 `plusCsValBinds` val_groups2
            , cs_typeds = typeds1 ++ typeds2
            , cs_fixds = fixds1 ++ fixds2 }            

instance (OutputableBndrId p) => Outputable (CsDecl (CsPass p)) where
  ppr (ValD _ bind) = ppr bind
  ppr (SigD _ sd) = ppr sd

type instance XCCsGroup (CsPass _) = NoExtField

emptyRnGroup :: CsGroup (CsPass p)
emptyRnGroup = emptyGroup { cs_valds = emptyValBindsOut }

emptyGroup :: CsGroup (CsPass p)
emptyGroup = CsGroup { cs_ext = noExtField
                     , cs_valds = error "emptyGroup cs_valds: Can't happen"
                     , cs_typeds = []
                     , cs_fixds = []
                     }

instance OutputableBndrId p => Outputable (CsGroup (CsPass p)) where
  ppr (CsGroup { cs_valds = val_decls, cs_typeds = type_decls, cs_fixds = fix_decls })
    = vcat_mb empty
      [ ppr_ds fix_decls
      , if isEmptyValBinds val_decls then Nothing else Just (ppr val_decls)
      , ppr_ds (typeGroupKindSigs type_decls)
      , ppr_ds (typeGroupTypeDecls type_decls)
      ]
    where
      ppr_ds :: Outputable a => [a] -> Maybe SDoc
      ppr_ds [] = Nothing
      ppr_ds ds = Just (vcat (map ppr ds))

      vcat_mb :: SDoc -> [Maybe SDoc] -> SDoc
      vcat_mb _ [] = empty
      vcat_mb gap (Nothing : ds) = vcat_mb gap ds
      vcat_mb gap (Just d : ds) = gap $$ d $$ vcat_mb blankLine ds

instance OutputableBndrId p => Outputable (TypeGroup (CsPass p)) where
  ppr (TypeGroup { group_typeds = typeds, group_kisigs = kisigs })
    = hang (text "TypeGroup") 2 $
      ppr kisigs $$ ppr typeds

pprTyDeclFlavor :: CsBind (CsPass p) -> SDoc
pprTyDeclFlavor (TyFunBind {}) = text "type"
pprTyDeclFlavor _ = panic "pprTyDeclFlavor"

emptyRdrGroup :: CsGroup (CsPass p)
emptyRdrGroup = emptyGroup { cs_valds = emptyValBindsIn }

csGroupTopLevelFixitySigs :: CsGroup (CsPass p) -> [LFixitySig (CsPass p)]
csGroupTopLevelFixitySigs (CsGroup { cs_fixds = fixds }) = fixds  

type instance XCTypeGroup (CsPass _) = NoExtField

typeDeclLName
  :: ( Anno (IdCsP p) ~ SrcSpanAnnN
     , OutputableBndrId p )
  => CsBind (CsPass p)
  -> LocatedN (IdP (CsPass p))
typeDeclLName (TyFunBind { tyfun_id = ln }) = ln
typeDeclLName other = pprPanic "typeDeclLName" (ppr other)

tydName
  :: ( Anno (IdCsP p) ~ SrcSpanAnnN
     , OutputableBndrId p )
  => CsBind (CsPass p)
  -> IdP (CsPass p)
tydName = unLoc . typeDeclLName

type instance Anno (CsDecl (CsPass _)) = SrcSpanAnnA
