{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CSlash.Cs.Binds
  ( module CSlash.Language.Syntax.Binds
  , module CSlash.Cs.Binds
  ) where

import CSlash.Language.Syntax.Binds

import CSlash.Language.Syntax.Extension
import CSlash.Cs.Extension
import CSlash.Parser.Annotation
import CSlash.Utils.Outputable

instance (OutputableBndrId pl, OutputableBndrId pr)
  => Outputable (CsBindLR (CsPass pl) (CsPass pr)) where
  ppr mbind = ppr_monobind mbind

ppr_monobind
  :: forall pl pr. (OutputableBndrId pl, OutputableBndrId pr)
  => CsBindLR (CsPass pl) (CsPass pr) -> SDoc
ppr_monoind (FunBind { fun_id = fun
                     , fun_matches = matches
                     , fun_ext = ext })
  = pprTicks empty ticksDoc
    $$ whenPprDebug (pprBndr LetBind (unLoc fun))
    $$ pprFunBind matches
    $$ whenPprDebug (pprIfTc @pr $ wrapDoc)
  where
    ticksDoc :: SDoc
    ticksDoc = case csPass @pr of
                 Ps -> empty
                 Rn -> empty
                 Tc | (_, ticks) <- ext ->
                      if null ticks
                      then empty
                      else text "-- ticks = " <> ppr ticks
    wrapDoc :: SDoc
    wrapDoc = case csPass @pr of
                Ps -> empty
                Rn -> empty
                Tc | (wrap, _) <- ext -> ppr wrap
ppr_monobind (TyFunBind _ _ _) = text "TyFunBind ppr non implemented"
ppr_monobind (VarBind { var_id = var, var_rhs = rhs })
  = sep [pprBndr CasePatBind var, nest 2 $ equal <+> pprExpr (unLoc rhs)]
