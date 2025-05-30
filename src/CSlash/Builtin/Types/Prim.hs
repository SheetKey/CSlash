module CSlash.Builtin.Types.Prim where

import {-# SOURCE #-} CSlash.Types.TyThing (mkATyCon)

import CSlash.Core.TyCon
import CSlash.Core.Type.Rep
import CSlash.Core.Kind

import CSlash.Types.Var
  ( TyVarBinder, TypeVar, KindVar
  , binderVar, binderVars
  , mkTyVar, mkKiVar
  , mkTyVarBinder, mkTyVarBinders )
import CSlash.Types.Name
import CSlash.Types.SrcLoc
import CSlash.Types.Unique

import CSlash.Builtin.Uniques
import CSlash.Builtin.Names
import CSlash.Utils.Misc ( changeLast )
import CSlash.Utils.Panic ( assertPpr )
import CSlash.Utils.Outputable
import CSlash.Utils.Trace

import CSlash.Data.FastString
import Data.Char

{- *********************************************************************
*                                                                      *
             Building blocks
*                                                                      *
********************************************************************* -}

mkPrimTc :: FastString -> Unique -> TyCon -> Name
mkPrimTc = mkGenPrimTc UserSyntax

mkGenPrimTc :: BuiltInSyntax -> FastString -> Unique -> TyCon -> Name
mkGenPrimTc built_in_syntax occ key tycon
  = mkWiredInName cSLASH_PRIM
                  (mkTcOccFS occ)
                  key
                  (mkATyCon tycon)
                  built_in_syntax

{- *********************************************************************
*                                                                      *
           Primitive type constructors
*                                                                      *
********************************************************************* -}

primTyCons :: [TyCon]
primTyCons = unexposedPrimTyCons ++ exposedPrimTyCons

unexposedPrimTyCons :: [TyCon]
unexposedPrimTyCons = []

exposedPrimTyCons :: [TyCon]
exposedPrimTyCons
  = [ fUNTyCon ]

{- *********************************************************************
*                                                                      *
                Type variables
*                                                                      *
********************************************************************* -}

mkTemplateKindVar :: KindVar
mkTemplateKindVar = mkKiVar $ mk_kv_name 0 "k"

mkTemplateKindVars :: Int -> [KindVar]
mkTemplateKindVars i
  = [ mkKiVar (mk_kv_name u ('k' : show u))
    | u <- [0..(i-1)]
    ]

mkTemplateKindVarsRes :: Int -> ([KindVar], KindVar)
mkTemplateKindVarsRes i
  = ( [ mkKiVar (mk_kv_name u ('k' : show u))
      | u <- [0..(i-1)]
      ]
    , mkKiVar (mk_kv_name i ('k' : show i)) )

mkTemplateFunKindVars :: Int -> [KindVar]
mkTemplateFunKindVars i
  = [ mkKiVar (mk_kv_name u ('k' : 'f' : show u))
    | u <- [0..(i-1)]
    ]

-- mkTemplateTyConKind :: Int -> Kind -> Kind
-- mkTemplateTyConKind arity res_kind
--   = let kind_vars = mkTemplateKindVars arity
--         kinds = KiVarKi <$> kind_vars
--         tc_kind = foldr (FunKd FKF_K_K) res_kind kinds
--     in tc_kind

mkTemplateTyConKindFromRes :: Int -> MonoKind -> Kind
mkTemplateTyConKindFromRes arity res_kind
  = let kind_vars = mkTemplateKindVars arity
        kinds = KiVarKi <$> kind_vars
        constraints = ((KiConApp LTEQKi) . (: [res_kind])) <$> kinds
        full_kind_no_constraints = foldr (FunKi FKF_K_K) res_kind kinds
        full_kind = foldr (FunKi FKF_C_K) full_kind_no_constraints constraints 
        q_full_kind = foldr ForAllKi (Mono full_kind) kind_vars
    in pprTrace "mkTemplateTyConKindFromRes" (ppr q_full_kind) q_full_kind

mkTemplateTyConKind :: Int -> Kind
mkTemplateTyConKind arity
  = let res_kind = KiVarKi $ mkKiVar (mk_kv_name arity ('k' : show arity))
    in mkTemplateTyConKindFromRes arity res_kind

mk_kv_name :: Int -> String -> Name
mk_kv_name u s = mkInternalName (mkAlphaTyVarUnique u)
                                (mkKiVarOccFS (mkFastString s))
                                noSrcSpan

mk_tv_name :: Int -> String -> Name
mk_tv_name u s = mkInternalName (mkAlphaTyVarUnique u)
                                (mkTyVarOccFS (mkFastString s))
                                noSrcSpan

mkTemplateTyVarsFrom :: Int -> [MonoKind] -> [TypeVar]
mkTemplateTyVarsFrom i kinds
  = [ mkTyVar name kind
    | (kind, index) <- zip kinds [0..(i-1)]
    , let ch_ord = index + ord 'a'
          name_str | ch_ord <= ord 'z' = [chr ch_ord]
                   | otherwise = 't':show index
          name = mk_tv_name (index + i + 1) name_str
    ]

mkTemplateTyVars :: [MonoKind] -> [TypeVar]
mkTemplateTyVars kinds = mkTemplateTyVarsFrom (length kinds) kinds

-- mkTemplateTyConBindersFrom :: Int -> [Kind] -> [TyConBinder]
-- mkTemplateTyConBindersFrom i kinds
--   = mkSpecifiedTyConBinders (mkTemplateTyVarsFrom i kinds)

-- mkTemplateTyConBinders :: [Kind] -> [TyConBinder]
-- mkTemplateTyConBinders kds = mkTemplateTyConBindersFrom (length kds) kds

-- mkTemplateTyConBindersKind :: Int -> ([TyConBinder], Kind, Kind)
-- mkTemplateTyConBindersKind arity
--   = let (kind_vars, res_kind_var) = mkTemplateKindVars arity
--         kinds = KiVarKi <$> kind_vars
--         res_kind = KiVarKi res_kind_var
--         tc_binders = mkTemplateTyConBinders kinds
--         tc_kind = foldr (FunKd FKF_K_K) res_kind kinds
--     in (tc_binders, res_kind, tc_kind)

{- *********************************************************************
*                                                                      *
                FunTyCon
*                                                                      *
********************************************************************* -}

-- this stuff seems wrong: "FUN" shouldn't have any constraints?
fUNTyConName :: Name
fUNTyConName = mkPrimTc (fsLit "FUN") fUNTyConKey fUNTyCon

fUNTyCon :: TyCon
fUNTyCon = mkPrimTyCon fUNTyConName tc_kind 2
  where
    tc_kind = mkTemplateTyConKind 2

unrestrictedFUNTyCon :: TyCon
unrestrictedFUNTyCon = _mkFUNTyCon (KiConApp UKd [])

affineFUNTyCon :: TyCon
affineFUNTyCon = _mkFUNTyCon (KiConApp AKd [])

linearFUNTyCon :: TyCon
linearFUNTyCon = _mkFUNTyCon (KiConApp LKd [])

_mkFUNTyCon :: MonoKind -> TyCon
_mkFUNTyCon res_kind = mkPrimTyCon fUNTyConName tc_kind 2
  where
    tc_kind = mkTemplateTyConKindFromRes 2 res_kind
