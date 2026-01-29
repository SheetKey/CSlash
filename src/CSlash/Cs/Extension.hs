{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module CSlash.Cs.Extension
  ( module X
  , module CSlash.Cs.Extension
  ) where

import {-# SOURCE #-} CSlash.Types.Var.Id

import CSlash.Language.Syntax.Extension

import CSlash.Cs.Pass as X

import CSlash.Parser.Annotation
import CSlash.Types.SrcLoc
import CSlash.Types.Name
import CSlash.Types.Name.Reader
import CSlash.Utils.Outputable
import CSlash.Utils.Panic.Plain

import Data.Data

type instance XRec (CsPass p) a = GenLocated (Anno a) a

type instance Anno RdrName = SrcSpanAnnN
type instance Anno Name = SrcSpanAnnN
type instance Anno (Id p) = SrcSpanAnnN

type IsSrcSpanAnn p a = (Anno (IdCsP p) ~ EpAnn a, NoAnn a, IsPass p)

instance UnXRec (CsPass p) where
  unXRec = unLoc

instance MapXRec (CsPass p) where
  mapXRec = fmap

type instance IdP (CsPass p) = IdCsP p

type family IdCsP pass where
  IdCsP 'Parsed = RdrName
  IdCsP 'Renamed = Name
  IdCsP 'Typechecked = Id Tc
  IdCsP 'Zonked = Id Zk

type instance NoTc (CsPass pass) = CsPass (NoCsTcPass pass)

type OutputableBndrId pass =
  ( OutputableBndr (IdCsP pass)
  , OutputableBndr (IdCsP (NoCsTcPass pass))
  , Outputable (GenLocated (Anno (IdCsP pass)) (IdCsP pass))
  , Outputable (GenLocated (Anno (IdCsP (NoCsTcPass pass))) (IdCsP (NoCsTcPass pass)))
  , IsPass pass
  )

pprIfPs :: forall p. IsPass p => (p ~ 'Parsed => SDoc) -> SDoc
pprIfPs pp = case csPass @p of Ps -> pp
                               _ -> empty

pprIfRn :: forall p. IsPass p => (p ~ 'Renamed => SDoc) -> SDoc
pprIfRn pp = case csPass @p of Rn -> pp
                               _ -> empty

pprIfTc :: forall p. IsPass p => (p ~ 'Typechecked => SDoc) -> SDoc
pprIfTc pp = case csPass @p of Tc -> pp
                               _ -> empty
