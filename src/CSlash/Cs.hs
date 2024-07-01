{-# LANGUAGE TypeFamilies #-}

module CSlash.Cs
  ( module CSlash.Language.Syntax
  , module CSlash.Cs.Doc
  , module CSlash.Cs.Expr
  , module CSlash.Cs.Extension
  , module CSlash.Cs.Kind
  , module CSlash.Cs.Lit
  , module CSlash.Cs.Pat
  , module CSlash.Cs.Type

  , CsModule(..), AnnsModule(..)
  , CsParsedModule(..), -- XModulePs(..)
  ) where
  
import CSlash.Language.Syntax
import CSlash.Cs.Doc
import CSlash.Cs.Expr
import CSlash.Cs.Extension
import CSlash.Cs.Kind
import CSlash.Cs.Lit
import CSlash.Cs.Pat
import CSlash.Cs.Type

import CSlash.Utils.Outputable
import CSlash.Types.SrcLoc

import Data.Data

-- data XModulePs = XModulePs
--   { csmodAnn :: EpAnn AnnsModule
--   , csmodLayout :: EpLayout
--   }
--   deriving (Data)

-- type instance XCModule Ps = XModulePs
-- type instance XCModule GhcRn = DataConCantHappen
-- type instance XCModule GhcTc = DataConCantHappen

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
    = pprMaybeWithDoc mbDoc $
      vcat
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
