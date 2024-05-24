module CSlash.Language.Syntax.ImpExp where

import CSlash.Langauge.Syntax.Extension
import CSlash.Language.Syntax.Module.Name

-- | Located Import or Export
type LIE pass = XRec pass (IE pass)

-- | Imported or exported entity
data IE pass
  = IEVar (XIEVar pass) (LIEWrappedName pass)
  | IEModuleContents (XIEModuleContents pass) (XRec pass ModuleName)

data IEWrappedName p
  = IEName (XIEName p) (LIdP p)
    
type LIEWrappedName p = XRec p (IEWrappedName p)
