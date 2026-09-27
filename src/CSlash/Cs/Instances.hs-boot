{-# LANGUAGE FlexibleInstances #-}

module CSlash.Cs.Instances where

import Data.Data hiding (Fixity)
import {-# SOURCE #-} CSlash.Cs.Expr
import CSlash.Cs.Pass

instance Data (CsExpr Ps)
instance Data (CsExpr Rn)
instance Data (CsExpr Tc)
instance Data (CsExpr Zk)
