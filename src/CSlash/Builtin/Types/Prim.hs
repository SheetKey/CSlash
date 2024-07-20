module CSlash.Builtin.Types.Prim where

import CSlash.Core.TyCon
import CSlash.Core.TyCo.Rep

import CSlash.Types.Var
  ( TyVarBinder, TyVar, binderVar, binderVars, mkTyVar, mkTyVarBinder, mkTyVarBinders )
import CSlash.Types.Name
import CSlash.Types.SrcLoc
import CSlash.Types.Unique

import CSlash.Builtin.Uniques
import CSlash.Builtin.Names
import CSlash.Utils.Misc ( changeLast )
import CSlash.Utils.Panic ( assertPpr )
import CSlash.Utils.Outputable

import CSlash.Data.FastString
import Data.Char

{- *********************************************************************
*                                                                      *
                Type variables
*                                                                      *
********************************************************************* -}

mkTemplateKindVar :: KindVar
mkTemplateKindVar = mkKdVar $ mk_kv_name 0 "k"

mkTemplateKindVars :: Int -> ([KindVar], KindVar)
mkTemplateKindVars i
  = ( [ mkKdVar (mk_kv_name u ('k' : show u))
      | u <- [0..(i-1)]
      ]
    , mkKdVar (mk_kv_name i ('k' : show i)) )

mk_kv_name :: Int -> String -> Name
mk_kv_name u s = mkInternalName (mkAlphasTyVarUnique u)
                                (mkTyVarOccFS (mkFastString s))
                                noSrcSpan

mk_tv_name :: Int -> String -> Name
mk_tv_name u s = mkInternalName (mkAlphasTyVarUnique u)
                                (mkTyVarOccFS (mkFastString s))
                                noSrcSpan

mkTemplateTyVarsFrom :: Int -> [Kind] -> [TyVar]
mkTemplateTyVarsFrom i kinds
  = [ mkTyVar name kind
    | (kind, index) <- zip kinds [0..(i-1)]
    , let ch_ord = index + ord 'a'
          name_str | ch_ord <= ord 'z' = [chr ch_ord]
                   | otherwise = 't':show index
          name = mk_tv_name (index + i + 1) name_str
    ]

mkTemplateTyConBindersFrom :: Int -> [Kind] -> [TyConBinder]
mkTemplateTyConBindersFrom i kinds
  = mkSpecifiedTyConBinders (mkTemplateTyVarsFrom i kinds)
