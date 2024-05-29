{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module CSlash.Cs.Extension where

import Data.Data

data CsPass (c :: Pass) where
  Ps :: CsPass 'Parsed
  Rn :: CsPass 'Renamed
  Tc :: CsPass 'Typechecked

data Pass = Parsed | Renamed | Typechecked
         deriving (Data)

type Ps = CsPass 'Parsed
type Rn = CsPass 'Renamed
type Tc = CsPass 'Typechecked

