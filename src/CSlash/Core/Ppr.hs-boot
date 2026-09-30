{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module CSlash.Core.Ppr where

import CSlash.Cs.Pass

import {-# SOURCE #-} CSlash.Core
import {-# SOURCE #-} CSlash.Types.Var.Id (Id)
import {-# SOURCE #-} CSlash.Types.Var.TyVar (TyVar)
import {-# SOURCE #-} CSlash.Types.Var.CoVar (KiCoVar)
import {-# SOURCE #-} CSlash.Types.Var.KiVar (KiVar)
import CSlash.Utils.Outputable (OutputableBndr, Outputable, SDoc)
import CSlash.Types.Fixity (LexicalFixity(..))

instance (OutputableBndr b1, OutputableBndr b2) => Outputable (Expr b1 b2)

instance HasPass p p' => OutputableBndr (Id (CsPass p'))
instance HasPass p p' => OutputableBndr (TyVar (CsPass p')) 
instance HasPass p p' => OutputableBndr (KiCoVar (CsPass p')) 
instance HasPass p p' => OutputableBndr (KiVar (CsPass p')) 

pprOcc :: OutputableBndr a => LexicalFixity -> a -> SDoc
