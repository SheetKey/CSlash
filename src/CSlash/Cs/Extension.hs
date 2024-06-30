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
import CSlash.Types.Name.Reader
import CSlash.Utils.Outputable

import Data.Data

type instance XRec (CsPass p) a = GenLocated (Anno a) a

type instance Anno RdrName = SrcSpanAnnN
type instance Anno Name = SrcSpanAnnN
-- type instance Anno Id = SrcSpanAnnN

instance UnXRec (CsPass p) where
  unXRec = unLoc

instance MapXRec (CsPass p) where
  mapXRec = fmap

data CsPass (c :: Pass) where
  Ps :: CsPass 'Parsed
  Rn :: CsPass 'Renamed
  Tc :: CsPass 'Typechecked

data Pass = Parsed | Renamed | Typechecked
         deriving (Data)

type Ps = CsPass 'Parsed
type Rn = CsPass 'Renamed
type Tc = CsPass 'Typechecked

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

type instance IdP (CsPass p) = IdCsP p

type family IdCsP pass where
  IdCsP 'Parsed = RdrName
  IdCsP 'Renamed = Name
  IdCsP 'Typechecked = () -- this should be 'Id'

type instance NoTc (CsPass pass) = CsPass (NoCsTcPass pass)

type family NoCsTcPass (p :: Pass) :: Pass where
  NoCsTcPass 'Typechecked = 'Renamed
  NoCsTcPass other = other

type OutputableBndrId pass =
  ( OutputableBndr (IdCsP pass)
  , OutputableBndr (IdCsP (NoCsTcPass pass))
  , Outputable (GenLocated (Anno (IdCsP pass)) (IdCsP pass))
  , Outputable (GenLocated (Anno (IdCsP (NoCsTcPass pass))) (IdCsP (NoCsTcPass pass)))
  , IsPass pass
  )
