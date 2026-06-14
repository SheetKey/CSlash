{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module CSlash.Stg.Syntax where

import Prelude hiding ((<>))

-- import GHC.Stg.InferTags.TagSig( TagSig )
import CSlash.Stg.Lift.Types

-- import GHC.Types.CostCentre ( CostCentreStack )

import CSlash.Core ( AltCon, CoreId, CoreType, CoreDataCon )
import CSlash.Core.DataCon
-- import CSlash.Core.TyCon ( PrimRep(..), PrimOrVoidRep(..), TyCon )
import CSlash.Core.Type ( Type )
import CSlash.Core.Ppr ({- instances -})

-- import GHC.Types.ForeignCall ( ForeignCall )
import CSlash.Types.Var
import CSlash.Types.Var.Id
import CSlash.Types.Tickish ( StgTickish )
import CSlash.Types.Var.Set
import CSlash.Types.Literal ( Literal, literalType )
-- import CSlash.Types.RepType ( typePrimRep, typePrimRep1, typePrimRepU, typePrimRep_maybe )

import CSlash.Utils.Outputable
import CSlash.Utils.Panic.Plain

-- import CSlash.Builtin.PrimOps ( PrimOp, PrimCall )

import Data.ByteString ( ByteString )
import Data.Data ( Data )
import Data.List ( intersperse )

{- *********************************************************************
*                                                                      *
GenStgBinding
*                                                                      *
********************************************************************* -}

data GenStgTopBinding pass
  = StgTopBind (GenStgBinding pass)
  | StgTopStringLit CoreId ByteString

data GenStgBinding pass
  = StgNonRec (BinderP pass) (GenStgRhs pass)
  | StgRec [(BinderP pass, GenStgRhs pass)]

{- *********************************************************************
*                                                                      *
StgArg
*                                                                      *
********************************************************************* -}

data StgArg
  = StgVarArg CoreId
  | StgLitArg Literal

stgArgType :: StgArg -> CoreType
stgArgType (StgVarArg v) = varType v
stgArgType (StgLitArg lit) = literalType lit

{- *********************************************************************
*                                                                      *
STG expressions
*                                                                      *
********************************************************************* -}

{- *********************************************************************
*                                                                      *
GenStgExpr
*                                                                      *
********************************************************************* -}

data GenStgExpr pass
  = StgApp CoreId [StgArg]

  | StgLit Literal

  | StgConApp CoreDataCon ConstructorNumber [StgArg]

  -- | StgOpApp StgOp [StgArg] CoreType
  
  | StgCase (GenStgExpr pass) (BinderP pass) AltType [GenStgAlt pass]

  | StgLet (XLet pass) (GenStgBinding pass) (GenStgExpr pass)

  -- Currently just for joins (I think)
  | StgLetNoEscape (XLetNoEscape pass) (GenStgBinding pass) (GenStgExpr pass)

  | StgTick StgTickish (GenStgExpr pass)

{- *********************************************************************
*                                                                      *
STG right-hand sides
*                                                                      *
********************************************************************* -}

data GenStgRhs pass
  = StgRhsClosure
    (XRhsClosure pass)
    [BinderP pass]
    (GenStgExpr pass)
    CoreType

  | StgRhsCon
    CoreDataCon
    ConstructorNumber
    [StgTickish]
    [StgArg]
    CoreType

data NoExtFieldSilent = NoExtFieldSilent
  deriving (Data, Eq, Ord)

instance Outputable NoExtFieldSilent where
  ppr _ = empty

noExtFieldSilent :: NoExtFieldSilent
noExtFieldSilent = NoExtFieldSilent

stgRhsArity :: StgRhs -> Int
stgRhsArity (StgRhsClosure _ bndrs _ _) = length bndrs
stgRhsArity StgRhsCon{} = 0

freeVarsOfRhs :: (XRhsClosure pass ~ DCoreIdSet) => GenStgRhs pass -> DCoreIdSet
freeVarsOfRhs (StgRhsClosure fvs _ _ _) = fvs
freeVarsOfRhs (StgRhsCon _ _ _ args _) = mkDVarSet [ id | StgVarArg id <- args ]

{- *********************************************************************
*                                                                      *
STG case alternatives
*                                                                      *
********************************************************************* -}

data GenStgAlt pass = GenStgAlt
  { alt_con :: !AltCon
  , alt_bndrs :: ![BinderP pass]
  , alt_rhs :: !(GenStgExpr pass)
  }

data AltType
  = MultiValAlt Int
  | PrimAlt

{- *********************************************************************
*                                                                      *
Plain STG parameterization
*                                                                      *
********************************************************************* -}

type StgTopBinding = GenStgTopBinding 'Vanilla
type StgBinding = GenStgBinding 'Vanilla
type StgExpr = GenStgExpr 'Vanilla
type StgRhs = GenStgRhs 'Vanilla
type StgAlt = GenStgAlt 'Vanilla

type LlStgTopBinding = GenStgTopBinding 'LiftLams
type LlStgBinding = GenStgBinding 'LiftLams
type LlStgExpr = GenStgExpr 'LiftLams
type LlStgRhs = GenStgRhs 'LiftLams
type LlStgAlt = GenStgAlt 'LiftLams

type CgStgTopBinding = GenStgTopBinding 'CodeGen
type CgStgBinding = GenStgBinding 'CodeGen
type CgStgExpr = GenStgExpr 'CodeGen
type CgStgRhs = GenStgRhs 'CodeGen
type CgStgAlt = GenStgAlt 'CodeGen

type InStgTopBinding = StgTopBinding
type InStgBinding = StgBinding
type InStgArg = StgArg
type InStgExpr = StgExpr
type InStgRhs = StgRhs
type InStgAlt = StgAlt
type OutStgTopBinding = StgTopBinding
type OutStgBinding = StgBinding
type OutStgArg = StgArg
type OutStgExpr = StgExpr
type OutStgRhs = StgRhs
type OutStgAlt = StgAlt

data ConstructorNumber = NoNumber | Numbered Int

instance Outputable ConstructorNumber where
  ppr NoNumber = empty
  ppr (Numbered n) = text "#" <> ppr n

data StgPass
  = Vanilla
  | LiftLams
  | CodeGen

type family BinderP (pass :: StgPass)
type instance BinderP 'Vanilla = CoreId
type instance BinderP 'LiftLams = BinderInfo
type instance BinderP 'CodeGen = CoreId

type family XRhsClosure (pass :: StgPass)
type instance XRhsClosure 'Vanilla = NoExtFieldSilent
type instance XRhsClosure 'LiftLams = DCoreIdSet 
type instance XRhsClosure 'CodeGen = DCoreIdSet

type family XLet (pass :: StgPass)
type instance XLet 'Vanilla = NoExtFieldSilent
type instance XLet 'LiftLams = Skeleton
type instance XLet 'CodeGen = NoExtFieldSilent

type family XLetNoEscape (pass :: StgPass)
type instance XLetNoEscape 'Vanilla = NoExtFieldSilent
type instance XLetNoEscape 'LiftLams = Skeleton
type instance XLetNoEscape 'CodeGen = NoExtFieldSilent

{- *********************************************************************
*                                                                      *
StgOp
*                                                                      *
********************************************************************* -}

data StgOp

{- *********************************************************************
*                                                                      *
Pretty printing
*                                                                      *
********************************************************************* -}

type OutputablePass pass
  = ( Outputable (XLet pass)
    , Outputable (XLetNoEscape pass)
    , Outputable (XRhsClosure pass)
    , OutputableBndr (BinderP pass) )

data StgPprOpts = StgPprOpts
  { stgSccEnabled :: !Bool }

panicStgPprOpts :: StgPprOpts 
panicStgPprOpts = StgPprOpts True

shortStgPprOpts :: StgPprOpts
shortStgPprOpts = StgPprOpts False

pprGenStgTopBinding
  :: OutputablePass pass
  => StgPprOpts -> GenStgTopBinding pass -> SDoc
pprGenStgTopBinding opts b = case b of
  StgTopStringLit bndr str
    -> hang (hsep [pprBndr LetBind bndr, equals]) 4 (pprCsBytes str <> semi)
  StgTopBind bind -> pprGenStgBinding opts bind

pprGenStgBinding :: OutputablePass pass => StgPprOpts -> GenStgBinding pass -> SDoc
pprGenStgBinding opts b = case b of
  StgNonRec bndr rhs -> hang (hsep [ pprBndr LetBind bndr, equals])
                        4 (pprStgRhs opts rhs <> semi)
  StgRec pairs -> vcat [ text "Rec {"
                       , vcat (intersperse blankLine (map ppr_bind pairs))
                       , text "end Rec }" ]
    where ppr_bind (bndr, expr)
            = hang (hsep [pprBndr LetBind bndr, equals])
              4 (pprStgRhs opts expr <> semi)

instance OutputablePass pass => Outputable (GenStgBinding pass) where
  ppr = pprGenStgBinding panicStgPprOpts

pprGenStgTopBindings
  :: OutputablePass pass
  => StgPprOpts -> [GenStgTopBinding pass] -> SDoc
pprGenStgTopBindings opts binds
  = vcat $ intersperse blankLine (map (pprGenStgTopBinding opts) binds)

pprStgBinding :: OutputablePass pass => StgPprOpts -> GenStgBinding pass -> SDoc
pprStgBinding = pprGenStgBinding

pprStgTopBinding :: OutputablePass pass => StgPprOpts -> GenStgTopBinding pass -> SDoc
pprStgTopBinding = pprGenStgTopBinding

pprStgTopBindings :: OutputablePass pass => StgPprOpts -> [GenStgTopBinding pass] -> SDoc
pprStgTopBindings = pprGenStgTopBindings

pprIdWithRep :: CoreId -> SDoc
pprIdWithRep v = ppr v <> pprTypeRep (varType v)

pprTypeRep :: CoreType -> SDoc
pprTypeRep ty = ppUnlessOption sdocSuppressStgReps $
  panic "pprTypeRep"

instance Outputable StgArg where
  ppr = pprStgArg

pprStgArg :: StgArg -> SDoc
pprStgArg (StgVarArg var) = pprIdWithRep var
pprStgArg (StgLitArg con) = ppr con <> pprTypeRep (literalType con)

instance OutputablePass pass => Outputable (GenStgExpr pass) where
  ppr = pprStgExpr panicStgPprOpts

pprStgExpr :: OutputablePass pass => StgPprOpts -> GenStgExpr pass -> SDoc
pprStgExpr opts e = case e of
  StgLit lit -> ppr lit
  StgApp func args -> hang (ppr func) 4 (interppSP args)
  StgConApp con n args -> hsep [ ppr con, ppr n, brackets (interppSP args) ]

  StgLet ext bind expr@StgLet{} ->
    (sep [hang (text "let" <+> ppr ext <+> text "{")
          2 (hsep [pprGenStgBinding opts bind, text "} in"])])
    $$ pprStgExpr opts expr

  StgLet ext bind expr
    -> sep [ hang (text "let" <+> ppr ext <+> text "{")
             2 (pprGenStgBinding opts bind)
           , hang (text "} in ") 2 (pprStgExpr opts expr) ]

  StgLetNoEscape ext bind expr
    -> sep [ hang (text "let-no-escape" <+> ppr ext <+> text "{")
             2 (pprGenStgBinding opts bind)
           , hang (text "} in ") 2 (pprStgExpr opts expr) ]

  StgTick tickish expr -> sdocOption sdocSuppressTicks $ \cond -> if cond
    then pprStgExpr opts expr
    else sep [ppr tickish, pprStgExpr opts expr]

  StgCase expr bndr alt_type alts
    -> sep [ sep [ text "case"
                 , nest 4 (hsep [ pprStgExpr opts expr
                                , whenPprDebug (colon <+> ppr alt_type) ])
                 , text "of"
                 , pprBndr CaseBind bndr
                 , char '{' ]
           , nest 2 (vcat (map (pprStgAlt opts True) alts))
           , char '}' ]

pprStgAlt :: OutputablePass pass => StgPprOpts -> Bool -> GenStgAlt pass -> SDoc
pprStgAlt opts indent GenStgAlt{ alt_con, alt_bndrs, alt_rhs }
  | indent = hang altPattern 4 (pprStgExpr opts alt_rhs <> semi)
  | otherwise = sep [altPattern, pprStgExpr opts alt_rhs <> semi]
  where altPattern = hsep [ ppr alt_con
                          , sep (map (pprBndr CasePatBind) alt_bndrs)
                          , text "->" ]

instance Outputable StgOp

instance Outputable AltType where
  ppr (MultiValAlt n) = text "MultiAlt" <+> ppr n
  ppr (PrimAlt) = text "Prim"

pprStgRhs :: OutputablePass pass => StgPprOpts -> GenStgRhs pass -> SDoc
pprStgRhs opts rhs = case rhs of
  StgRhsClosure ext args body _
    -> hang (hsep [ ppUnlessOption sdocSuppressStgExts (ppr ext)
                  , char '\\', brackets (interppSP args) ])
       4 (pprStgExpr opts body)

  StgRhsCon con mid _ args _
    -> hcat [ case mid of
                NoNumber -> empty
                Numbered n -> hcat [ppr n, space]
            , ppr con
            , text "! "
            , brackets (sep (map pprStgArg args)) ]

instance OutputablePass pass => Outputable (GenStgRhs pass) where
  ppr = pprStgRhs panicStgPprOpts
