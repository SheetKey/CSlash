module CSlash.IfaceToCore where

import CSlash.Iface.Syntax ( IfaceDecl{-, IfaceDefault, IfaceClsInst, IfaceFamInst, IfaceRule
                           , IfaceAnnotation-}, IfaceCompleteMatch )
import CSlash.Types.TyThing   ( TyThing )
import CSlash.Tc.Types        ( IfG, IfL )
-- import GHC.Core.InstEnv    ( ClsInst )
-- import GHC.Core.FamInstEnv ( FamInst )
-- import GHC.Core         ( CoreRule )
import CSlash.Types.CompleteMatch
-- import GHC.Types.Annotations ( Annotation )
-- import GHC.Types.DefaultEnv ( ClassDefaults )
import CSlash.Types.Name
import CSlash.Unit.Types      ( Module )
import CSlash.Utils.Fingerprint
import CSlash.Types.Var (TyVar, KiVar)

import Data.List.NonEmpty ( NonEmpty )

tcIfaceCompleteMatches :: [IfaceCompleteMatch] -> IfL CompleteMatches
tcIfaceDecls :: Bool -> [(Fingerprint, IfaceDecl)] -> IfL [(Name, TyThing (TyVar KiVar) KiVar)]
