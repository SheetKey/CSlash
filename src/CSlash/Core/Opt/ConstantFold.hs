{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module CSlash.Core.Opt.ConstantFold (builtinRules) where

-- import GHC.Platform
-- import GHC.Float

-- import GHC.Types.Id.Make ( unboxedUnitExpr )
-- import GHC.Types.Id
-- import GHC.Types.Literal
-- import GHC.Types.Name.Occurrence ( occNameFS )
-- import GHC.Types.Tickish
-- import GHC.Types.Name ( Name, nameOccName )
-- import GHC.Types.Basic

import CSlash.Core
-- import GHC.Core.Make
-- import GHC.Core.SimpleOpt (  exprIsConApp_maybe, exprIsLiteral_maybe )
-- import GHC.Core.DataCon ( DataCon,dataConTagZ, dataConTyCon, dataConWrapId, dataConWorkId )
-- import GHC.Core.Utils  ( cheapEqExpr, exprIsHNF
--                        , stripTicksTop, stripTicksTopT, mkTicks )
-- import GHC.Core.Multiplicity
-- import GHC.Core.Rules.Config
-- import GHC.Core.Type
-- import GHC.Core.TyCo.Compare( eqType )
-- import GHC.Core.TyCon
--    ( TyCon, tyConDataCons_maybe, tyConDataCons, tyConFamilySize
--    , isEnumerationTyCon, isValidDTT2TyCon, isNewTyCon )
-- import GHC.Core.Map.Expr ( eqCoreExpr )

-- import GHC.Builtin.PrimOps ( PrimOp(..), tagToEnumKey )
-- import GHC.Builtin.PrimOps.Ids (primOpId)
-- import GHC.Builtin.Types
-- import GHC.Builtin.Types.Prim
-- import GHC.Builtin.Names

-- import GHC.Cmm.MachOp ( FMASign(..) )
-- import GHC.Cmm.Type ( Width(..) )

-- import GHC.Data.FastString
-- import GHC.Data.Maybe      ( orElse )

-- import GHC.Utils.Outputable
-- import GHC.Utils.Misc
-- import GHC.Utils.Panic

-- import Control.Applicative ( Alternative(..) )
-- import Control.Monad
-- import Data.Functor (($>))
-- import qualified Data.ByteString as BS
-- import Data.Ratio
-- import Data.Word
-- import Data.Maybe (fromMaybe, fromJust)

builtinRules :: [CoreRule]
builtinRules = []
