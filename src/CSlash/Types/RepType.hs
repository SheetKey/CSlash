{-# LANGUAGE MultiWayIf #-}

module CSlash.Types.RepType
  ( module CSlash.Types.RepType
  , PrimRep(..)
  ) where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Types.Basic (Arity, RepArity)
import CSlash.Types.Unique
import CSlash.Types.Var
import CSlash.Core.DataCon
import CSlash.Core.TyCon
import CSlash.Core.Type.Rep
import CSlash.Core.Type
import CSlash.Builtin.Names

import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Monad
import CSlash.Data.Maybe (orElse)

import Data.List.NonEmpty (NonEmpty (..))
import Data.List (sort)
import qualified Data.IntSet as IS

{- **********************************************************************
*                                                                       *
                Representation types
*                                                                       *
********************************************************************** -}

type NvUnaryType = Type Zk
type UnaryType = Type Zk

isNvUnaryRep :: [PrimRep] -> Bool
isNvUnaryRep [_] = True
isNvUnaryRep _ = False

unwrapType :: HasPass p pass => Type p -> Type p
unwrapType ty = inner_ty
  where
    inner_ty = go ty

    go t | Just t' <- coreView t = go t'
    go (ForAllTy _ t) = go t
    go (CastTy t _) = go t
    go t = t

countFunRepArgs :: HasPass p pass => Arity -> Type p -> RepArity
countFunRepArgs 0 _ = 0
countFunRepArgs n ty
  | FunTy _ _arg res <- unwrapType ty
  = 1                                 -- (length (typePrimRep arg) `max` 1)
    + countFunRepArgs (n - 1) res
  | otherwise
  = pprPanic "countFunRepArgs arity greater than type can handle" (ppr (n, ty))

isZeroBitTy :: HasDebugCallStack => Type Zk -> Bool
isZeroBitTy ty = fmap null (typePrimRep_maybe ty) `orElse` False

{- **********************************************************************
*                                                                       *
                   Unboxed sums
*                                                                       *
********************************************************************** -}

type SortedSlotTys = [SlotTy]

data SlotTy
  = WordSlot Int -- IntIRep, UIntIRep, AddrRep
  | FloatSlot
  | DoubleSlot
  deriving (Eq, Ord)

instance Outputable SlotTy where
  ppr (WordSlot i) = text "WordSlot" <> int i
  ppr FloatSlot = text "FloatSlot"
  ppr DoubleSlot = text "DoubleSlot"
 
repSlotTy :: [PrimRep] -> Maybe SlotTy
repSlotTy reps = case reps of
  [] -> Nothing
  [rep] -> Just (primRepSlot rep)
  _ -> pprPanic "repSlotTy" (ppr reps)

primRepSlot :: PrimRep -> SlotTy
primRepSlot (IntRep i) = WordSlot i
primRepSlot (UIntRep i) = WordSlot i
primRepSlot AddrRep = WordSlot 64 -- TODO: pointer size?
primRepSlot FloatRep = FloatSlot
primRepSlot DoubleRep = DoubleSlot

slotPrimRep :: SlotTy -> PrimRep
slotPrimRep (WordSlot i) = UIntRep i
slotPrimRep FloatSlot = FloatRep
slotPrimRep DoubleSlot = DoubleRep

sumRepType :: [[PrimRep]] -> NonEmpty SlotTy
sumRepType constrs0
  | constrs0 `lengthLessThan` 2
  = panic "shouldn't happen"
  | otherwise
  = let combine_alts :: [SortedSlotTys] -> SortedSlotTys
        combine_alts constrs = foldl' merge [] constrs

        merge :: SortedSlotTys -> SortedSlotTys -> SortedSlotTys
        merge existing_slots [] = existing_slots
        merge [] needed_slots = needed_slots
        merge (es : ess) (s : ss)
          | Just s' <- s `fitsIn` es
          = s' : merge ess ss
          | s < es
          = s : merge (es : ess) ss
          | otherwise
          = es : merge ess (s : ss)

        rep :: [PrimRep] -> SortedSlotTys
        rep ty = sort (map primRepSlot ty)

    in WordSlot 64 :| combine_alts (map rep constrs0) -- TODO: tag slot size??

layoutSum
  :: HasDebugCallStack
  => SortedSlotTys
  -> [SlotTy]
  -> [Int]
layoutSum sum_slots0 arg_slots0 = go arg_slots0 IS.empty
  where
    go :: [SlotTy] -> IS.IntSet -> [Int]
    go [] _ = []
    go (arg : args) used = let slot_idx = findSlot arg 0 sum_slots0 used
                           in slot_idx : go args (IS.insert slot_idx used)

    findSlot :: SlotTy -> Int -> SortedSlotTys -> IS.IntSet -> Int
    findSlot arg slot_idx (slot : slots) useds
      | not (IS.member slot_idx useds)
      , Just slot == arg `fitsIn` slot
      = slot_idx
      | otherwise
      = findSlot arg (slot_idx + 1) slots useds
    findSlot _ _ [] _
      = pprPanic "findSlot" (text "Can't find slot"
                              $$ text "sum_slots:" <> ppr sum_slots0
                              $$ text "arg_slots:" <> ppr arg_slots0)

fitsIn :: SlotTy -> SlotTy -> Maybe SlotTy
fitsIn ty1 ty2
  | ty1 == ty2
  = Just ty1
  | isWordSlot ty1 && isWordSlot ty2
  = Just (max ty1 ty2)
  | otherwise
  = Nothing
  where
    isWordSlot (WordSlot _) = True
    isWordSlot _ = False

{- **********************************************************************
*                                                                       *
                   PrimRep
*                                                                       *
********************************************************************** -}

typePrimRep :: HasDebugCallStack => Type Zk -> [PrimRep]
typePrimRep ty = typePrimRep_maybe ty `orElse` pprPanic "typePrimRep" (ppr ty)

typePrimRep_maybe :: HasDebugCallStack => Type Zk -> Maybe [PrimRep]
typePrimRep_maybe ty
  -- Tuple type
  | Just (tc, tys) <- splitTyConApp_maybe ty
  , isTupleTyCon tc
  = concatMapM typePrimRep_maybe tys
  -- Sum type
  | Just (tc, tys) <- splitTyConApp_maybe ty
  , isSumTyCon tc
  = pprPanic "typePrimRep on sum" (ppr ty)

  -- Special tuple/sum types
  -- | Just (tc, tys) <- splitTyConApp_maybe ty
  -- , tc `hasKey` ioResTyConKey
  -- , [_ki, ty] <- tys
  -- = typePrimRep_maybe ty
         
  | Just (tc, tys) <- splitTyConApp_maybe ty
  , tc `hasKey` ioTyConKey
  , [_ki, _fki, ty] <- tys
  = typePrimRep_maybe ty 

  -- Function types
  | Just (tc, _) <- splitTyConApp_maybe ty
  , tc `hasKey` fUNTyConKey
  = Just [AddrRep] -- TODO: runtime rep of functions???

  -- Builtins (can have kind and coercion args, but no type args)
  | Just (tc, tys) <- splitTyConApp_maybe ty
  = assertPpr (all isKindOrCoArg tys) (ppr tc $$ ppr tys) $ -- assertion may go away if comptime/type lits are allowed
    if | tc `hasKey` boolTyConKey
         -> Just [IntRep 1]
       | tc `hasKey` realWorldTyConKey
         -> Just []
       -- if 'tc `hasKey` fUNTyConKey' then should we return 'AddrRep'?
       | otherwise
         -> pprPanic "typePrimRep unknown TyCon" (ppr tc $$ ppr tys)

  -- Necessary to make tupel/sum cases easier
  | Embed{} <- ty
  = Just []
  | KindCoercion{} <- ty
  = Just []

  -- Deal with stuff for 'isZeroBitTy' called in core2core
  | TyVarTy{} <- ty
  = Nothing
  | BigTyLamTy _ ty' <- ty
  = typePrimRep_maybe ty'
  | ForAllKiCo _ ty' <- ty
  = typePrimRep_maybe ty'
  | ForAllTy {} <- ty
  = Nothing

  | otherwise
  = pprPanic "typePrimRep_maybe" (ppr ty)

typePrimRep1 :: HasDebugCallStack => UnaryType -> PrimOrVoidRep
typePrimRep1 ty = case typePrimRep ty of
  [] -> VoidRep
  [rep] -> NVRep rep
  _ -> pprPanic "typePrimRep1" (ppr ty $$ ppr (typePrimRep ty))

typePrimRepU :: HasDebugCallStack => NvUnaryType -> PrimRep
typePrimRepU ty = case typePrimRep ty of
  [rep] -> rep
  _ -> pprPanic "typePrimRepU" (ppr ty $$ ppr (typePrimRep ty))

isKindOrCoArg :: Type Zk -> Bool
isKindOrCoArg Embed{} = True
isKindOrCoArg KindCoercion{} = True
isKindOrCoArg _ = False

primRepToType :: PrimRep -> Type Zk
primRepToType = panic "primRepToType"
