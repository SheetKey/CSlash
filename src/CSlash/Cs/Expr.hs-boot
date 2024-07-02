{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-} -- Wrinkle in Note [Trees That Grow]
                                      -- in module Language.Haskell.Syntax.Extension

{-# OPTIONS_GHC -Wno-orphans #-} -- Outputable

module CSlash.Cs.Expr where

import CSlash.Utils.Outputable ( SDoc, Outputable )
import CSlash.Language.Syntax.Expr
  ( CsExpr, LCsExpr
  , MatchGroup
  , GRHSs
  )
import CSlash.Cs.Extension ( OutputableBndrId, CsPass )
import CSlash.Types.Name   ( Name )
import Data.Bool  ( Bool )
import Data.Maybe ( Maybe )

instance (OutputableBndrId p) => Outputable (CsExpr (CsPass p))

pprLExpr :: (OutputableBndrId p) => LCsExpr (CsPass p) -> SDoc

pprExpr :: (OutputableBndrId p) => CsExpr (CsPass p) -> SDoc

pprFunBind :: (OutputableBndrId idR)
           => MatchGroup (CsPass idR) (LCsExpr (CsPass idR)) -> SDoc
