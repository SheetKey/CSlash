{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Unfold where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Core as Core
import CSlash.Core.Utils
import CSlash.Core.DataCon
import CSlash.Core.Type

import CSlash.Types.Var.Id
import CSlash.Types.Var.Class
import CSlash.Types.Literal
import CSlash.Types.Var.Id.Info
-- import CSlash.Types.RepType ( isZeroBitTy )
import CSlash.Types.Basic  ( Arity, RecFlag )
-- import GHC.Types.ForeignCall
import CSlash.Types.Tickish

-- import GHC.Builtin.PrimOps
import CSlash.Builtin.Names
import CSlash.Data.Bag
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Data.Maybe (mapMaybe)
import qualified Data.ByteString as BS

-- TODO: Void and () are zerobit
isZeroBitTy _ = False

data UnfoldingOpts = UnfoldingOpts
  { unfoldingCreationThreshold :: !Int
  , unfoldingUseThreshold :: !Int
  , unfoldingFunAppDiscount :: !Int
  , unfoldingDictDiscount :: !Int
  , unfoldingVeryAggressive :: !Bool
  , unfoldingCaseThreshold :: !Int
  , unfoldingCaseScaling :: !Int
  , unfoldingReportPrefix :: !(Maybe String)
  }

defaultUnfoldingOpts :: UnfoldingOpts
defaultUnfoldingOpts = UnfoldingOpts
  { unfoldingCreationThreshold = 750
  , unfoldingUseThreshold = 90
  , unfoldingFunAppDiscount = 60
  , unfoldingDictDiscount = 30
  , unfoldingVeryAggressive = False
  , unfoldingCaseThreshold = 2
  , unfoldingCaseScaling = 30
  , unfoldingReportPrefix = Nothing
  }

updateCreationThreshold :: Int -> UnfoldingOpts -> UnfoldingOpts
updateCreationThreshold n opts = opts { unfoldingCreationThreshold = n }

updateUseThreshold :: Int -> UnfoldingOpts -> UnfoldingOpts
updateUseThreshold n opts = opts { unfoldingUseThreshold = n }

updateFunAppDiscount :: Int -> UnfoldingOpts -> UnfoldingOpts
updateFunAppDiscount n opts = opts { unfoldingFunAppDiscount = n }

updateDictDiscount :: Int -> UnfoldingOpts -> UnfoldingOpts
updateDictDiscount n opts = opts { unfoldingDictDiscount = n }

updateVeryAggressive :: Bool -> UnfoldingOpts -> UnfoldingOpts
updateVeryAggressive n opts = opts { unfoldingVeryAggressive = n }

updateCaseThreshold :: Int -> UnfoldingOpts -> UnfoldingOpts
updateCaseThreshold n opts = opts { unfoldingCaseThreshold = n }

updateCaseScaling :: Int -> UnfoldingOpts -> UnfoldingOpts
updateCaseScaling n opts = opts { unfoldingCaseScaling = n }

updateReportPrefix :: Maybe String -> UnfoldingOpts -> UnfoldingOpts
updateReportPrefix n opts = opts { unfoldingReportPrefix = n }

data ArgSummary
  = TrivArg
  | NonTrivArg
  | ValueArg

instance Outputable ArgSummary where
  ppr TrivArg    = text "TrivArg"
  ppr NonTrivArg = text "NonTrivArg"
  ppr ValueArg   = text "ValueArg"

nonTriv ::  ArgSummary -> Bool
nonTriv TrivArg = False
nonTriv _       = True

data CallCtxt      
  = BoringCtxt     
  | RhsCtxt RecFlag
  | DiscArgCtxt    
  | RuleArgCtxt    
  | ValAppCtxt     
  | CaseCtxt       

instance Outputable CallCtxt where
  ppr CaseCtxt = text "CaseCtxt"
  ppr ValAppCtxt = text "ValAppCtxt"
  ppr BoringCtxt = text "BoringCtxt"
  ppr (RhsCtxt ir) = text "RhsCtxt" <> parens (ppr ir)
  ppr DiscArgCtxt = text "DiscArgCtxt"
  ppr RuleArgCtxt = text "RuleArgCtxt"

{- *********************************************************************
*                                                                      *
              The UnfoldingGuidance type
*                                                                      *
********************************************************************* -}

calcUnfoldingGuidance
  :: UnfoldingOpts
  -> Bool
  -> Bool
  -> CoreExpr
  -> UnfoldingGuidance
calcUnfoldingGuidance opts is_top_bottoming is_join (Tick t expr)
  | not (tickishIsCode t)
  = calcUnfoldingGuidance opts is_top_bottoming is_join expr
calcUnfoldingGuidance opts is_top_bottoming is_join expr
  = case sizeExpr opts bOMB_OUT_SIZE val_bndrs body of
      TooBig -> UnfNever
      SizeIs size cased_bndrs scrut_discount
        | uncondInline is_join expr bndrs n_val_bndrs body size
        -> UnfWhen { ug_unsat_ok = True
                   , ug_boring_ok = True
                   , ug_arity = n_val_bndrs }
        | is_top_bottoming
        -> UnfNever

        | otherwise
        -> UnfIfGoodArgs { ug_args = map (mk_discount cased_bndrs) val_bndrs
                         , ug_size = size
                         , ug_res = scrut_discount }
  where
    (bndrs_kis, body) = collectBinders expr
    bOMB_OUT_SIZE = unfoldingCreationThreshold opts

    bndrs = fst $ unzip bndrs_kis
    val_bndrs = mapMaybe runtimeVar_maybe bndrs
    n_val_bndrs = length val_bndrs

    mk_discount :: Bag (CoreId, Int) -> CoreId -> Int
    mk_discount cbs bndr = foldl' combine 0 cbs
      where
        combine acc (bndr', disc)
          | bndr == bndr' = acc `plus_disc` disc
          | otherwise = acc
        plus_disc | isFunTy (varType bndr) = max
                  | otherwise = (+)

uncondInline :: Bool -> CoreExpr -> [CoreBndr] -> Arity -> CoreExpr -> Int -> Bool
uncondInline is_join rhs bndrs arity body size
  | is_join = uncondInlineJoin bndrs body
  | arity > 0 = size <= 10 * (arity + 1)
  | otherwise = exprIsTrivial rhs

uncondInlineJoin :: [CoreBndr] -> CoreExpr -> Bool
uncondInlineJoin _ body
  | exprIsTrivial body
  = True
  | (Var v, args) <- collectArgs body
  , all exprIsTrivial args
  , isJoinId v
  = True
  | otherwise
  = False

sizeExpr
  :: UnfoldingOpts
  -> Int
  -> [CoreId]
  -> CoreExpr
  -> ExprSize
sizeExpr opts !bOMB_OUT_SIZE top_args expr
  = size_up expr
  where
    size_up (Cast e _) = size_up e
    size_up (Tick _ e) = size_up e
    size_up (Type _) = sizeZero
    size_up (KiCo _) = sizeZero
    size_up (Kind _) = sizeZero
    size_up (Lit lit) = sizeN (litSize lit)
    size_up (Var f) | isZeroBitId f = sizeZero
                    | otherwise = size_up_call f [] 0
    size_up (App fun arg)
      | isNonValArg arg = size_up fun
      | otherwise = size_up arg `addSizeNSD`
                    size_up_app fun [arg] (if isZeroBitExpr arg then 1 else 0)
    size_up (Lam b k e)
      | Core.Id id <- b
      , not (isZeroBitId id)
      = lamScrutDiscount opts (size_up e `addSizeN` 10)
      | otherwise = size_up e
    size_up (Let (NonRec binder rhs) body)
      = size_up_rhs (binder, rhs) `addSizeNSD`
        size_up body
    size_up (Let (Rec pairs) body)
      = foldr (addSizeNSD . size_up_rhs) (size_up body) pairs
    size_up (Case e _ _ alts)
      | null alts
      = panic "empty case"
      | Just v <- is_top_arg e
      = let alt_sizes = map size_up_alt alts
            alts_size (SizeIs tot tot_disc tot_scrut) (SizeIs max _ _)
              = SizeIs tot (unitBag (v, 20 + tot - max) `unionBags` tot_disc) tot_scrut

            alts_size tot_size _ = tot_size
        in alts_size (foldr1 addAltSize alt_sizes) (foldr1 maxSize alt_sizes)
      | otherwise
      = size_up e `addSizeNSD` foldr (addAltSize . size_up_alt) case_size alts
      where
        is_top_arg (Var v) | v `elem` top_args = Just v
        is_top_arg (Cast e _) = is_top_arg e
        is_top_arg _ = Nothing

        case_size
          | is_inline_scrut e, lengthAtMost alts 1 = sizeN (-10)
          | otherwise = sizeZero

        is_inline_scrut (Var v) = True -- TODO: all types unlifted? maybe should be false?

        is_inline_scrut scrut
          | (Var f, _) <- collectArgs scrut
          = case idDetails f of
              -- TODO: primopid or foreighncall fcallid
              _ -> False
          | otherwise
          = False

    size_up_rhs (bndr, rhs)
      | JoinPoint join_arity <- idJoinPointHood bndr
      , (_, body) <- collectNBinders join_arity rhs
      = size_up body
      | otherwise
      = size_up rhs

    size_up_app (App fun arg) args voids
      | isNonValArg arg = size_up_app fun args voids
      | isZeroBitExpr arg = size_up_app fun (arg:args) (voids + 1)
      | otherwise = size_up arg `addSizeNSD`
                    size_up_app fun (arg:args) voids
    size_up_app (Var fun) args voids = size_up_call fun args voids
    size_up_app (Tick _ expr) args voids = size_up_app expr args voids
    size_up_app (Cast expr _) args voids = size_up_app expr args voids
    size_up_app other args voids = size_up other `addSizeN` callSize (length args) voids

    size_up_call :: CoreId -> [CoreExpr] -> Int -> ExprSize
    size_up_call fun val_args voids
      = case idDetails fun of
          DataConId dc -> conSize dc (length val_args)
          _ -> funSize opts top_args fun (length val_args) voids
          -- TODO: foreigncall and primopid

    size_up_alt (Alt _ _ rhs) = size_up rhs `addSizeN` 10

    addSizeN TooBig _ = TooBig
    addSizeN (SizeIs n xs d) m = mkSizeIs bOMB_OUT_SIZE (n + m) xs d

    addAltSize TooBig _ = TooBig
    addAltSize _ TooBig = TooBig
    addAltSize (SizeIs n1 xs d1) (SizeIs n2 ys d2)
      = mkSizeIs bOMB_OUT_SIZE (n1 + n2) (xs `unionBags` ys) (d1 + d2)

    addSizeNSD TooBig _ = TooBig
    addSizeNSD _ TooBig = TooBig
    addSizeNSD (SizeIs n1 xs _) (SizeIs n2 ys d2)
      = mkSizeIs bOMB_OUT_SIZE (n1 + n2) (xs `unionBags` ys) d2

    isZeroBitId id = not (isJoinId id) && isZeroBitTy (varType id)

    isZeroBitExpr (Var id) = isZeroBitId id
    isZeroBitExpr (Tick _ e) = isZeroBitExpr e
    isZeroBitExpr _ = False

litSize :: Literal -> Int
litSize _ = panic "litSize"

callSize :: Int -> Int -> Int
callSize n_val_args voids = 10 * (1 + n_val_args - voids)

jumpSize :: Int -> Int -> Int
jumpSize _ _ = 0

funSize :: UnfoldingOpts -> [CoreId] -> CoreId -> Int -> Int -> ExprSize
funSize opts top_args fun n_val_args voids
  = SizeIs size arg_discount res_discount
  where
    some_val_args = n_val_args > 0
    is_join = isJoinId fun

    size | is_join = jumpSize n_val_args voids
         | not some_val_args = 0
         | otherwise = callSize n_val_args voids

    arg_discount | some_val_args && fun `elem` top_args
                 = unitBag (fun, unfoldingFunAppDiscount opts)
                 | otherwise
                 = emptyBag

    res_discount | idArity fun > n_val_args = unfoldingFunAppDiscount opts
                 | otherwise = 0

conSize :: DataCon Zk -> Int -> ExprSize
conSize dc n_val_args
  | n_val_args == 0 = SizeIs 0 emptyBag 10
  | isTupleDataCon dc = SizeIs 0 emptyBag 10
  | otherwise = SizeIs 10 emptyBag 10

lamScrutDiscount :: UnfoldingOpts -> ExprSize -> ExprSize
lamScrutDiscount opts (SizeIs n vs _) = SizeIs n vs (unfoldingFunAppDiscount opts)
lamScrutDiscount _ TooBig = TooBig

data ExprSize
  = TooBig
  | SizeIs { _es_size_is :: {-# UNPACK #-} !Int
           , _es_args :: !(Bag (CoreId, Int))
           , _es_discount :: {-# UNPACK #-} !Int
           }

instance Outputable ExprSize where
  ppr TooBig = text "TooBig"
  ppr (SizeIs a _ c) = brackets (int a <+> int c)

mkSizeIs :: Int -> Int -> Bag (CoreId, Int) -> Int -> ExprSize
mkSizeIs max n xs d | (n - d) > max = TooBig
                    | otherwise = SizeIs n xs d

maxSize :: ExprSize -> ExprSize -> ExprSize
maxSize TooBig _ = TooBig
maxSize _ TooBig = TooBig
maxSize s1@(SizeIs n1 _ _) s2@(SizeIs n2 _ _) | n1 > n2 = s1
                                              | otherwise = s2

sizeZero :: ExprSize
sizeZero = SizeIs 0 emptyBag 0                                  

sizeN :: Int -> ExprSize
sizeN n = SizeIs n emptyBag 0
