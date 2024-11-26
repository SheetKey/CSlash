{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

module CSlash.Cs.Utils where

import CSlash.Cs.Decls
import CSlash.Cs.Binds
import CSlash.Cs.Expr
import CSlash.Cs.Pat
import CSlash.Cs.Type
import CSlash.Cs.Lit
import CSlash.Language.Syntax.Decls
import CSlash.Language.Syntax.Extension
import CSlash.Cs.Extension
import CSlash.Parser.Annotation

import CSlash.Core.DataCon
import CSlash.Core.Type ( Type )

import CSlash.Types.Id
import CSlash.Types.Name
import CSlash.Types.Name.Set hiding ( unitFV )
import CSlash.Types.Name.Env
import CSlash.Types.Name.Reader
import CSlash.Types.Var
import CSlash.Types.Basic
import CSlash.Types.SrcLoc
import CSlash.Types.Fixity
import CSlash.Types.SourceText

import CSlash.Data.FastString
import CSlash.Data.Bag

import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Control.Arrow ( first )
import Data.Foldable ( toList )
import Data.List ( partition )
import Data.List.NonEmpty ( nonEmpty )
import qualified Data.List.NonEmpty as NE

import Data.IntMap ( IntMap )
import qualified Data.IntMap.Strict as IntMap
import Data.Map ( Map )
import qualified Data.Map.Strict as Map

{- *********************************************************************
*                                                                      *
        Some useful helpers for constructing syntax
*                                                                      *
********************************************************************* -}

unguardedGRHSs
  :: Anno (GRHS (CsPass p) (LocatedA (body (CsPass p))))
     ~ EpAnn NoEpAnns
  => SrcSpan
  -> LocatedA (body (CsPass p))
  -> EpAnn GrhsAnn
  -> GRHSs (CsPass p) (LocatedA (body (CsPass p)))
unguardedGRHSs loc rhs an = GRHSs emptyComments (unguardedRHS an loc rhs)

unguardedRHS
  :: Anno (GRHS (CsPass p) (LocatedA (body (CsPass p))))
     ~ EpAnn NoEpAnns
  => EpAnn GrhsAnn
  -> SrcSpan
  -> LocatedA (body (CsPass p))
  -> [LGRHS (CsPass p) (LocatedA (body (CsPass p)))]
unguardedRHS an loc rhs = [L (noAnnSrcSpan loc) (GRHS an [] rhs)]

type UtilsAnnoBody p body
  = ( XMG (CsPass p) (LocatedA (body (CsPass p))) ~ Origin
    , Anno [LocatedA (Match (CsPass p) (LocatedA (body (CsPass p))))] ~ SrcSpanAnnL
    , Anno (Match (CsPass p) (LocatedA (body (CsPass p)))) ~ SrcSpanAnnA
    )

mkMatchGroup
  :: UtilsAnnoBody p body
  => Origin
  -> LocatedL [LocatedA (Match (CsPass p) (LocatedA (body (CsPass p))))]
  -> MatchGroup (CsPass p) (LocatedA (body (CsPass p)))
mkMatchGroup origin matches = MG { mg_ext = origin
                                 , mg_alts = matches }

mkLamMatchGroup
  :: UtilsAnnoBody p body
  => Origin
  -> LocatedL [LocatedA (Match (CsPass p) (LocatedA (body (CsPass p))))]
  -> MatchGroup (CsPass p) (LocatedA (body (CsPass p)))
mkLamMatchGroup origin (L l matches)
  = mkMatchGroup origin (L l $ map fixCtxt matches)
  where
    fixCtxt (L a match) = L a match{ m_ctxt = LamAlt }

mkTyLamMatchGroup
  :: UtilsAnnoBody p body
  => Origin
  -> LocatedL [LocatedA (Match (CsPass p) (LocatedA (body (CsPass p))))]
  -> MatchGroup (CsPass p) (LocatedA (body (CsPass p)))
mkTyLamMatchGroup origin (L l matches)
  = mkMatchGroup origin (L l $ map fixCtxt matches)
  where
    fixCtxt (L a match) = L a match{ m_ctxt = TyLamAlt }

mkTyLamTyMatchGroup
  :: UtilsAnnoBody p body
  => Origin
  -> LocatedL [LocatedA (Match (CsPass p) (LocatedA (body (CsPass p))))]
  -> MatchGroup (CsPass p) (LocatedA (body (CsPass p)))
mkTyLamTyMatchGroup origin (L l matches)
  = mkMatchGroup origin (L l $ map fixCtxt matches)
  where
    fixCtxt (L a match) = L a match{ m_ctxt = TyLamTyAlt }

mkCsIntegral :: IntegralLit -> CsOverLit Ps
mkCsIntegral i = OverLit noExtField (CsIntegral i)

mkCsFractional :: FractionalLit -> CsOverLit Ps
mkCsFractional f = OverLit noExtField (CsFractional f)

mkCsIsString :: SourceText -> FastString -> CsOverLit Ps
mkCsIsString src s = OverLit noExtField (CsIsString src s)

mkCsIf :: LCsExpr Ps -> LCsExpr Ps -> LCsExpr Ps -> AnnsIf -> CsExpr Ps
mkCsIf c a b anns = CsIf anns c a b

mkNPat :: LocatedAn NoEpAnns (CsOverLit Ps) -> Maybe (SyntaxExpr Ps) -> [AddEpAnn] -> Pat Ps
mkNPat lit neg anns = NPat anns lit neg noSyntaxExpr

mkBodyStmt :: LocatedA (bodyR Ps) -> StmtLR (CsPass idL) Ps (LocatedA (bodyR Ps))
mkBodyStmt body = BodyStmt noExtField body

mkPsBindStmt
  :: [AddEpAnn]
  -> LPat Ps
  -> LocatedA (bodyR Ps)
  -> StmtLR Ps Ps (LocatedA (bodyR Ps))
mkPsBindStmt ann pat body = BindStmt ann pat body

mkLetStmt :: [AddEpAnn] -> CsLocalBinds Ps -> StmtLR Ps Ps (LocatedA b)
mkLetStmt anns binds = LetStmt anns binds

{- *********************************************************************
*                                                                      *
              Constructing syntax with no location info
*                                                                      *
********************************************************************* -}

nl_CsVar :: IsSrcSpanAnn p a => IdP (CsPass p) -> CsExpr (CsPass p)
nl_CsVar n = CsVar noExtField (noLocA n)

missingTupArg :: EpAnn Bool -> CsTupArg Ps
missingTupArg ann = Missing ann

{- *********************************************************************
*                                                                      *
        LCsSigType
*                                                                      *
********************************************************************* -}

csTypeToCsSigType :: LCsType Ps -> LCsSigType Ps
csTypeToCsSigType lty@(L loc ty) =
  L (l2l loc) $ CsSig noExtField lty

{- *********************************************************************
*                                                                      *
        Collecting binders
*                                                                      *
********************************************************************* -}

collectCsIdBinders
  :: CollectPass (CsPass idL)
  => CollectFlag (CsPass idL)
  -> CsValBindsLR (CsPass idL) (CsPass idR)
  -> [IdP (CsPass idL)]
collectCsIdBinders flag = collect_cs_val_binders True flag

collectCsValBinders
  :: CollectPass (CsPass idL)
  => CollectFlag (CsPass idL)
  -> CsValBindsLR (CsPass idL) (CsPass idR)
  -> [IdP (CsPass idL)]
collectCsValBinders flag = collect_cs_val_binders False flag

collectCsBindsBinders :: CollectPass p => CollectFlag p -> LCsBindsLR p idR -> [IdP p]
collectCsBindsBinders flag binds = collect_binds False flag binds []

collect_cs_val_binders
  :: CollectPass (CsPass idL)
  => Bool
  -> CollectFlag (CsPass idL)
  -> CsValBindsLR (CsPass idL) (CsPass idR)
  -> [IdP (CsPass idL)]
collect_cs_val_binders ps flag = \case
  ValBinds _ binds _ -> collect_binds ps flag binds []
  XValBindsLR (NValBinds binds _) -> collect_out_binds ps flag binds

collect_out_binds
  :: CollectPass p
  => Bool
  -> CollectFlag p
  -> [(RecFlag, LCsBinds p)]
  -> [IdP p]
collect_out_binds ps flag = foldr (collect_binds ps flag . snd) []

collect_binds
  :: forall p idR. CollectPass p
  => Bool
  -> CollectFlag p
  -> LCsBindsLR p idR
  -> [IdP p]
  -> [IdP p]  
collect_binds ps flag binds acc = foldr (collect_bind ps flag . unXRec @p) acc binds

collect_bind
  :: forall p idR. CollectPass p
  => Bool
  -> CollectFlag p
  -> CsBindLR p idR
  -> [IdP p]
  -> [IdP p]
collect_bind _ _ (FunBind { fun_id = f }) acc = unXRec @p f : acc
collect_bind _ _ (XCsBindsLR b) acc = collectXXCsBindsLR @p @idR b acc
collect_bind _ _ _ _ = panic "collect_bind" 

collectPatBinders
  :: CollectPass p
  => CollectFlag p
  -> LPat p
  -> [IdP p]
collectPatBinders flag pat = collect_lpat flag pat []
  
collectPatsBinders
  :: CollectPass p
  => CollectFlag p
  -> [LPat p]
  -> [IdP p]
collectPatsBinders flag pats = foldr (collect_lpat flag) [] pats


data CollectFlag p where
  CollNoDictBinders :: CollectFlag p
  CollVarTyVarBinders :: CollectFlag Rn

collect_lpat
  :: forall p. CollectPass p
  => CollectFlag p
  -> LPat p
  -> [IdP p]
  -> [IdP p]
collect_lpat flag pat bndrs = collect_pat flag (unXRec @p pat) bndrs

collect_pat
  :: forall p. CollectPass p
  => CollectFlag p
  -> Pat p
  -> [IdP p]
  -> [IdP p]
collect_pat flag pat bndrs = case pat of
  VarPat _ var -> unXRec @p var : bndrs
  TyVarPat _ tv -> case flag of
    CollNoDictBinders -> bndrs
    CollVarTyVarBinders -> unXRec @p tv : bndrs
  WildPat _ -> bndrs
  AsPat _ a pat -> unXRec @p a : collect_lpat flag pat bndrs
  ParPat _ pat -> collect_lpat flag pat bndrs
  TuplePat _ pats -> foldr (collect_lpat flag) bndrs pats
  SumPat _ pat _ _ -> collect_lpat flag pat bndrs
  ConPat {pat_args = ps} -> case flag of
    CollNoDictBinders -> foldr (collect_lpat flag) bndrs (csConPatArgs ps)
    CollVarTyVarBinders -> foldr (collect_lpat flag) bndrs (csConPatArgs ps)
                           ++ concatMap collectConPatTyArgBndrs (csConPatTyArgs ps)
  LitPat _ _ -> bndrs
  NPat {} -> bndrs
  SigPat _ pat sig -> case flag of
    CollNoDictBinders -> collect_lpat flag pat bndrs
    CollVarTyVarBinders -> collect_lpat flag pat bndrs ++ collectPatSigBndrs sig
  KdSigPat _ pat _ -> case flag of
    CollNoDictBinders -> bndrs
    CollVarTyVarBinders -> collect_lpat flag pat bndrs
  ImpPat _ pat -> case flag of
    CollNoDictBinders -> bndrs
    CollVarTyVarBinders -> collect_lpat flag pat bndrs
  XPat ext -> collectXXPat @p flag ext bndrs  

collectConPatTyArgBndrs :: CsConPatTyArg Rn -> [Name]
collectConPatTyArgBndrs (CsConPatTyArg _ tp) = collectTyPatBndrs tp

collectTyPatBndrs :: CsTyPat Rn -> [Name]
collectTyPatBndrs (CsTP (CsTPRn nwcs imp_tvs exp_tvs) _) = nwcs ++ imp_tvs ++ exp_tvs

collectPatSigBndrs :: CsPatSigType Rn -> [Name]
collectPatSigBndrs (CsPS (CsPSRn imp_tvs) _) = imp_tvs

class UnXRec p => CollectPass p where
  collectXXPat :: CollectFlag p -> XXPat p -> [IdP p] -> [IdP p]
  collectXXCsBindsLR :: forall pR. XXCsBindsLR p pR -> [IdP p] -> [IdP p]

instance IsPass p => CollectPass (CsPass p) where
  collectXXPat flag ext =
    case csPass @p of
      Ps -> dataConCantHappen ext
      Rn | CsPatExpanded _ pat <- ext
           -> collect_pat flag pat
      Tc -> case ext of
        ExpansionPat _ pat -> collect_pat flag pat
  collectXXCsBindsLR ext =
    case csPass @p of
      Ps -> dataConCantHappen ext
      Rn -> dataConCantHappen ext
      Tc -> case ext of
        AbsBinds { abs_exports = dbinds } -> (map abe_poly dbinds ++)

csTyForeignBinders :: [TypeGroup Rn] -> [Name]
csTyForeignBinders type_decls = panic "csTyForeignBinders"

-------------------

data TyDeclBinders p = TyDeclBinders
  { tyDeclMainBinder :: !(LocatedA (IdP (CsPass p)), TyConFlavor ())
  -- , tyDeclATs :: ![(LocatedA (IdP (CsPass p)), TyConFlavor ())]       -- ATs=associated types
  -- , tyDeclOpSigs :: ![LocatedA (IdP (CsPass p))]                      -- class op sigs
  }

csLTyDeclBinders
  :: (IsPass p, OutputableBndrId p) => LocatedA (CsBind (CsPass p)) -> TyDeclBinders p
csLTyDeclBinders (L loc (TyFunBind { tyfun_id = (L _ name) }))
  = TyDeclBinders { tyDeclMainBinder = (L loc name, TypeFunFlavor) }
csLTyDeclBinders b = pprPanic "csLTyDeclBinders" (ppr b)
