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

module CSlash.Cs.Extension where

import CSlash.Language.Syntax.Extension

import CSlash.Parser.Annotation
import CSlash.Types.SrcLoc
import CSlash.Types.Name
import CSlash.Types.Var
import CSlash.Types.Name.Reader
import CSlash.Utils.Outputable
import CSlash.Utils.Panic.Plain

import Data.Data

type instance XRec (CsPass p) a = GenLocated (Anno a) a

type instance Anno RdrName = SrcSpanAnnN
type instance Anno Name = SrcSpanAnnN
type instance Anno (Id tv kv) = SrcSpanAnnN
type instance Anno (Var tv kv) = SrcSpanAnnN

type IsSrcSpanAnn p a = (Anno (IdCsP p) ~ EpAnn a, NoAnn a, IsPass p)

instance UnXRec (CsPass p) where
  unXRec = unLoc

instance MapXRec (CsPass p) where
  mapXRec = fmap

data CsPass (c :: Pass) where
  Ps :: CsPass 'Parsed
  Rn :: CsPass 'Renamed
  Tc :: CsPass 'Typechecked
  Zk :: CsPass 'Zonked

instance Typeable p => Data (CsPass p) where
  gunfold _ _ _ = panic "instance Data CsPass"
  toConstr _ = panic "instance Data CsPass"
  dataTypeOf _ = panic "instance Data CsPass"

data Pass = Parsed | Renamed | Typechecked | Zonked
  deriving (Data)

type Ps = CsPass 'Parsed
type Rn = CsPass 'Renamed
type Tc = CsPass 'Typechecked
type Zk = CsPass 'Zonked

class ( NoCsTcPass (NoCsTcPass p) ~ NoCsTcPass p
      , IsPass (NoCsTcPass p)
      ) => IsPass p where
  csPass :: CsPass p

instance IsPass 'Parsed where
  csPass = Ps

instance IsPass 'Renamed where
  csPass = Rn

instance IsPass 'Typechecked where
  csPass = Tc

instance IsPass 'Zonked where
  csPass = Zk

type instance IdP (CsPass p) = IdCsP p

type family IdCsP pass where
  IdCsP 'Parsed = RdrName
  IdCsP 'Renamed = Name
  IdCsP 'Typechecked = (Id (AnyTyVar AnyKiVar) AnyKiVar)
  IdCsP 'Zonked = (Id (TyVar KiVar) KiVar)

type instance NoTc (CsPass pass) = CsPass (NoCsTcPass pass)

type family NoCsTcPass (p :: Pass) :: Pass where
  NoCsTcPass 'Typechecked = 'Renamed
  NoCsTcPass 'Zonked = 'Renamed
  NoCsTcPass other = other

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
