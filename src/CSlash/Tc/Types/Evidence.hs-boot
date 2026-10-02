{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RoleAnnotations #-}

module CSlash.Tc.Types.Evidence where

import CSlash.Cs.Pass
import CSlash.Utils.Outputable

type role CsWrapper nominal
data CsWrapper p

-- instance HasPass p p' => Outputable (CsWrapper (CsPass p')) 

pprCsWrapper :: HasPass p pass => CsWrapper p -> (Bool -> SDoc) -> SDoc
