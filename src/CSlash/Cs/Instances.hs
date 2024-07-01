{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -O0 #-}

module CSlash.Cs.Instance where

import Data.Data

import CSlash.Hs.Extension
import CSlash.Hs.Binds
import CSlash.Hs.Decls
import CSlash.Hs.Expr
import CSlash.Hs.Lit
import CSlash.Hs.Type
import CSlash.Hs.Pat
import CSlash.Hs.ImpExp
import CSlash.Parser.Annotation

deriving instance Data (Sig Ps)
deriving instance Data (Sig Rn)
deriving instance Data (Sig Tc)

deriving instance Data (CsDecl Ps)
deriving instance Data (CsDecl Rn)
deriving instance Data (CsDecl Tc)

deriving instance Data (MatchGroup Ps (LocatedA (CsExpr Ps)))
deriving instance Data (MatchGroup Rn (LocatedA (CsExpr Rn)))
deriving instance Data (MatchGroup Tc (LocatedA (CsExpr Tc)))

deriving instance Data (Match Ps (LocatedA (CsExpr Ps)))
deriving instance Data (Match Rn (LocatedA (CsExpr Rn)))
deriving instance Data (Match Tc (LocatedA (CsExpr Tc)))

deriving instance Data (GRHSs Ps (LocatedA (CsExpr Ps)))
deriving instance Data (GRHSs Rn (LocatedA (CsExpr Rn)))
deriving instance Data (GRHSs Tc (LocatedA (CsExpr Tc)))

deriving instance Data (GRHS Ps (LocatedA (CsExpr Ps)))
deriving instance Data (GRHS Rn (LocatedA (CsExpr Rn)))
deriving instance Data (GRHS Tc (LocatedA (CsExpr Tc)))

deriving instance Data (StmtLR Ps Ps (LocatedA (CsExpr Ps)))
deriving instance Data (StmtLR Ps Rn (LocatedA (CsExpr Rn)))
deriving instance Data (StmtLR Rn Rn (LocatedA (CsExpr Rn)))
deriving instance Data (StmtLR Tc Tc (LocatedA (CsExpr Tc)))

deriving instance Data (CsLit Ps)
deriving instance Data (CsLit Rn)
deriving instance Data (CsLit Tc)

deriving instance Data (Pat Ps)
deriving instance Data (Pat Rn)
deriving instance Data (Pat Tc)

deriving instance Data (CsSigType Ps)
deriving instance Data (CsSigType Rn)
deriving instance Data (CsSigType Tc)

deriving instance Data (CsPatSigType Ps)
deriving instance Data (CsPatSigType Rn)
deriving instance Data (CsPatSigType Tc)

deriving instance Data (CsTyPat Ps)
deriving instance Data (CsTyPat Rn)
deriving instance Data (CsTyPat Tc)

deriving instance Data (CsForAllTelescope Ps)
deriving instance Data (CsForAllTelescope Rn)
deriving instance Data (CsForAllTelescope Tc)

deriving instance Data (CsTyVarBndr Ps)
deriving instance Data (CsTyVarBndr Rn)
deriving instance Data (CsTyVarBndr Tc)

deriving instance Data (CsType Ps)
deriving instance Data (CsType Rn)
deriving instance Data (CsType Tc)

deriving instance Data (CsArrow Ps)
deriving instance Data (CsArrow Rn)
deriving instance Data (CsArrow Tc)

deriving instance Data (ImportDecl Ps)
deriving instance Data (ImportDecl Rn)
deriving instance Data (ImportDecl Tc)

deriving instance Data (IE Ps)
deriving instance Data (IE Rn)
deriving instance Data (IE Tc)

deriving instance Eq (IE Ps)
deriving instance Eq (IE Rn)
deriving instance Eq (IE Tc)
