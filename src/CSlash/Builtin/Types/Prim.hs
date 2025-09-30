module CSlash.Builtin.Types.Prim where

import {-# SOURCE #-} CSlash.Types.TyThing (mkATyCon)
import {-# SOURCE #-} CSlash.Core.Type (buildSynTyCon, mkTyConApp, typeKind)

import CSlash.Core.TyCon
import CSlash.Core.Type.Rep
import CSlash.Core.Kind

import CSlash.Types.Var
  ( TyVarBinder, TyVar, KiVar
  , binderVar, binderVars
  , mkTyVar, mkKiVar
  , mkVarBinder, mkVarBinders )
import CSlash.Types.Name
import CSlash.Types.SrcLoc
import CSlash.Types.Unique

import CSlash.Builtin.Uniques
import CSlash.Builtin.Names
import CSlash.Utils.Misc ( changeLast )
import CSlash.Utils.Panic ( panic, assertPpr )
import CSlash.Utils.Outputable
import CSlash.Utils.Trace

import CSlash.Data.FastString
import Data.Char

{- *********************************************************************
*                                                                      *
             Building blocks
*                                                                      *
********************************************************************* -}

type PTyCon = TyCon PTyVar KiVar
type PMonoKind = MonoKind KiVar
type PType = Type PTyVar KiVar
type PKind = Kind KiVar
type PTyVar = TyVar KiVar

mkPrimTc :: FastString -> Unique -> PTyCon -> Name
mkPrimTc = mkGenPrimTc UserSyntax

mkGenPrimTc :: BuiltInSyntax -> FastString -> Unique -> PTyCon -> Name
mkGenPrimTc built_in_syntax occ key tycon
  = mkWiredInName cSLASH_BUILTIN
                  (mkTcOccFS occ)
                  key
                  (mkATyCon tycon)
                  built_in_syntax

{- *********************************************************************
*                                                                      *
           Primitive type constructors
*                                                                      *
********************************************************************* -}

primTyCons :: [PTyCon]
primTyCons = unexposedPrimTyCons ++ exposedPrimTyCons

unexposedPrimTyCons :: [PTyCon]
unexposedPrimTyCons = [ eqTyCon ]

exposedPrimTyCons :: [PTyCon]
exposedPrimTyCons
  = [ fUNTyCon ]

{- *********************************************************************
*                                                                      *
                Type variables
*                                                                      *
********************************************************************* -}

mkTemplateKindVar :: KiVar
mkTemplateKindVar = mkKiVar $ mk_kv_name 0 "k"

mkTemplateKindVars :: Int -> [KiVar]
mkTemplateKindVars i
  = [ mkKiVar (mk_kv_name u ('k' : show u))
    | u <- [0..(i-1)]
    ]

mkTemplateKindVarsRes :: Int -> ([KiVar], KiVar)
mkTemplateKindVarsRes i
  = ( [ mkKiVar (mk_kv_name u ('k' : show u))
      | u <- [0..(i-1)]
      ]
    , mkKiVar (mk_kv_name i ('k' : show i)) )

mkTemplateFunKindVars :: Int -> [KiVar]
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

mkTemplateTyConKindFromRes :: Int -> PMonoKind -> PKind
mkTemplateTyConKindFromRes arity res_kind
  = let kind_vars = mkTemplateKindVars arity
        kinds = KiVarKi <$> kind_vars
        constraints = (flip (KiPredApp LTEQKi) res_kind) <$> kinds
        full_kind_no_constraints = foldr (FunKi FKF_K_K) res_kind kinds
        full_kind = foldr (FunKi FKF_C_K) full_kind_no_constraints constraints
        res_kind_var = case res_kind of
                         KiVarKi var -> [var]
                         _ -> []
        q_full_kind = foldr ForAllKi (Mono full_kind) (kind_vars ++ res_kind_var)
    in pprTrace "mkTemplateTyConKindFromRes" (ppr q_full_kind) q_full_kind

mkTemplateTyConKind :: Int -> PKind
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

mkTemplateTyVarsFrom :: Int -> [PMonoKind] -> [PTyVar]
mkTemplateTyVarsFrom i kinds
  = [ mkTyVar name kind
    | (kind, index) <- zip kinds [0..(i-1)]
    , let ch_ord = index + ord 'a'
          name_str | ch_ord <= ord 'z' = [chr ch_ord]
                   | otherwise = 't':show index
          name = mk_tv_name (index + i + 1) name_str
    ]

mkTemplateTyVars :: [PMonoKind] -> [PTyVar]
mkTemplateTyVars kinds = mkTemplateTyVarsFrom (length kinds) kinds

mkTemplateKiCoVarsFrom :: Int -> [PMonoKind] -> [PTyVar]
mkTemplateKiCoVarsFrom i kinds
  = [ mkTyVar name kind
    | (kind, index) <- zip kinds [0..(i-1)]
    , let name_str = "kco" ++ show index
          name = mk_kv_name (index + i + 1) name_str
    ]

mkTemplateKiCoVars :: [PMonoKind] -> [PTyVar]
mkTemplateKiCoVars kinds = mkTemplateKiCoVarsFrom (length kinds) kinds

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

fUNTyCon :: PTyCon
fUNTyCon = mkPrimTyCon fUNTyConName tc_kind 2
  where
    tc_kind = mkTemplateTyConKind 2

unrestrictedFUNTyCon :: PTyCon
unrestrictedFUNTyCon = _mkFUNTyCon (BIKi UKd)

affineFUNTyCon :: PTyCon
affineFUNTyCon = _mkFUNTyCon (BIKi AKd)

linearFUNTyCon :: PTyCon
linearFUNTyCon = _mkFUNTyCon (BIKi LKd)

_mkFUNTyCon :: PMonoKind -> PTyCon
_mkFUNTyCon res_kind = mkPrimTyCon fUNTyConName tc_kind 2
  where
    tc_kind = mkTemplateTyConKindFromRes 2 res_kind

{- *********************************************************************
*                                                                      *
                Equality constraints
*                                                                      *
********************************************************************* -}

eqTyConName :: Name
eqTyConName = mkPrimTc (fsLit "~") eqTyConKey eqTyCon

eqTyCon :: PTyCon
eqTyCon = mkPrimTyCon eqTyConName kind 2
  where
    (k1, k2) = case mkTemplateKindVars 2 of
                 [k1, k2] -> (k1, k2)
                 _ -> undefined
    -- forall k1 k2. k1 -> k2 -> UKd
    kind = ForAllKi k1
           $ ForAllKi k2
           $ Mono
           $ FunKi FKF_K_K (KiVarKi k1)
           $ FunKi FKF_K_K (KiVarKi k2)
           $ BIKi UKd

{- *********************************************************************
*                                                                      *
                IO
*                                                                      *
********************************************************************* -}

realWorldTyConName :: Name
realWorldTyConName = mkPrimTc (fsLit "RealWorld#") realWorldTyConKey realWorldTyCon

realWorldTyCon :: PTyCon
realWorldTyCon = mkPrimTyCon realWorldTyConName (Mono (BIKi LKd)) 0

ioResTyConName :: Name
ioResTyConName = mkPrimTc (fsLit "IORes") ioResTyConKey ioResTyCon

ioResTyCon :: PTyCon
ioResTyCon = mkPrimTyCon ioResTyConName kind 1
  where
    kva = case mkTemplateKindVars 1 of
            [k1] -> k1
            _ -> panic "unreachable"

    -- This is essentially a '(a : k, World# : LKd) : LKd'
    kind = ForAllKi kva $
           Mono $
           FunKi FKF_K_K (KiVarKi kva) (BIKi LKd)

primIoTyConName :: Name
primIoTyConName = mkPrimTc (fsLit "PrimIO") primIoTyConKey primIoTyCon

primIoTyCon :: PTyCon
primIoTyCon = buildSynTyCon primIoTyConName kind 1 rhs
  where
    kva = case mkTemplateKindVars 1 of
            [k1] -> k1
            _ -> panic "unreachable"
    kvf = case mkTemplateFunKindVars 1 of
            [k] -> k
            _ -> panic "unreachable"

    tva = case mkTemplateTyVars [mkKiVarKi kva] of
            [tv] -> tv
            _ -> panic "unreachable"

    kind = typeKind rhs

    -- /\kva kvf -> \a : kva -> (World# : LKd) -kvf> (IORes kva a : LKd)
    -- Values of this type are kvf functions from linear World#
    -- to linear World# paired with a kva value.
    rhs = BigTyLamTy kva $
          BigTyLamTy kvf $
          TyLamTy tva $
          FunTy (KiVarKi kvf)
                (mkTyConTy realWorldTyCon)
                (mkTyConApp ioResTyCon [ Embed (KiVarKi kva), TyVarTy tva ])

ioTyConName :: Name
ioTyConName = mkPrimTc (fsLit "IO") ioTyConKey ioTyCon

ioTyCon :: PTyCon
ioTyCon = mkPrimTyCon ioTyConName kind 1
  where
    (kva, kvb) = case mkTemplateKindVars 2 of
            [k1, k2] -> (k1, k2)
            _ -> panic "unreachable"

    kind = ForAllKi kva $ ForAllKi kvb $ Mono $
           FunKi FKF_K_K (KiVarKi kva) (KiVarKi kvb)
