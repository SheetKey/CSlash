{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module CSlash.Cs.Decls
  ( CsDecl(..), LCsDecl(..)

  , partitionBindsAndSigs
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

instance (OutputableBndrId p) => Outputable (CsDecl (CsPass p)) where
  ppr (ValD _ bind) = ppr bind
  ppr (SigD _ sd) = ppr sd

type instance Anno (CsDecl (CsPass _)) = SrcSpanAnnA
