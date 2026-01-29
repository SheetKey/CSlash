{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

module CSlash.Cs.Pass where

import CSlash.Utils.Panic 

import Data.Data

type HasPass p p' = (p ~ CsPass p', IsPass p')

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

type family NoCsTcPass (p :: Pass) :: Pass where
  NoCsTcPass 'Typechecked = 'Renamed
  NoCsTcPass 'Zonked = 'Renamed
  NoCsTcPass other = other

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
