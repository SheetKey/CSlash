{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module CSlash.Cs
  ( module CSlash.Language.Syntax
  , module CSlash.Cs.Doc
  , module CSlash.Cs.Binds
  , module CSlash.Cs.Decls
  , module CSlash.Cs.Expr
  , module CSlash.Cs.Extension
  , module CSlash.Cs.Kind
  , module CSlash.Cs.Lit
  , module CSlash.Cs.Pat
  , module CSlash.Cs.Type
  , module CSlash.Cs.Utils
  , module CSlash.Cs.ImpExp

  , module CSlash.Parser.Annotation

  , CsModule(..), AnnsModule(..)
  , CsParsedModule(..), XModulePs(..)
  ) where
  
import CSlash.Language.Syntax
import CSlash.Cs.Doc
import CSlash.Cs.Binds
import CSlash.Cs.Decls
import CSlash.Cs.Expr
import CSlash.Cs.Extension
import CSlash.Cs.Kind
import CSlash.Cs.Lit
import CSlash.Cs.Pat
import CSlash.Cs.Type
import CSlash.Cs.Utils
import CSlash.Cs.ImpExp

import CSlash.Cs.Instances

import CSlash.Utils.Outputable
import CSlash.Types.SrcLoc
import CSlash.Parser.Annotation

import Data.Data

data XModulePs = XModulePs
  { csmodAnn :: EpAnn AnnsModule
  , csmodLayout :: EpLayout
  }
  deriving (Data)

type instance XCModule Ps = XModulePs
type instance XCModule Rn = DataConCantHappen
type instance XCModule Tc = DataConCantHappen

type instance Anno ModuleName = SrcSpanAnnA

deriving instance Data (CsModule Ps)

data AnnsModule = AnnsModule
  { am_main :: [AddEpAnn]
  , am_decls :: [TrailingAnn]
  , am_cs :: [LEpaComment]
  , am_eof :: Maybe (RealSrcSpan, RealSrcSpan)
  }
  deriving (Data, Eq)

instance Outputable (CsModule Ps) where
  ppr (CsModule { csmodName = name
                , csmodExports = exports
                , csmodImports = imports
                , csmodDecls = decls })
    = vcat
      [ case exports of
          Nothing -> pp_header (text "where")
          Just es -> vcat
                     [ pp_header lparen
                     , nest 8 (pprWithCommas ppr (unLoc es))
                     , nest 4 (text ") where")
                     ]
      , pp_nonnull imports
      , pp_nonnull decls
      ]
    where
      pp_header rest = pp_modname <+> rest
      pp_modname = text "module" <+> ppr name

pp_nonnull :: Outputable t => [t] -> SDoc
pp_nonnull [] = empty
pp_nonnull xs = vcat (map ppr xs)

data CsParsedModule = CsParsedModule
  { cpm_module :: Located (CsModule Ps)
  , cpm_src_files :: [FilePath]
  }
