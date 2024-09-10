{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module CSlash.Cs.Stats where

import CSlash.Data.Bag
import CSlash.Cs
import CSlash.Types.SrcLoc

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic

import Data.Char

ppSourceStats :: Bool -> Located (CsModule Ps) -> SDoc
ppSourceStats
  short (L _ (CsModule{ csmodExports = exports, csmodImports = imports, csmodDecls = ldecls }))
  = (if short then hcat else vcat)
    (map pp_val
      [ ("ExportAll        ", export_all)
      , ("ExportDecls      ", export_ds)
      , ("ExportModules    ", export_ms)
      , ("Imports          ", imp_no)
      , ("  ImpQual        ", imp_qual)
      , ("  ImpAs          ", imp_as)
      , ("  ImpAll         ", imp_all)
      , ("  ImpPartial     ", imp_partial)
      , ("  ImpHiding      ", imp_hiding)
      , ("FixityDecls      ", fixity_sigs)
      , ("TypeDecls        ", ty_bind_ds)
      , ("TypeSigs         ", bind_tys)
      , ("FunBinds         ", fn_bind_ds)
      ])
  where
    decls = map unLoc ldecls

    pp_val (_, 0) = empty
    pp_val (str, n)
      | not short = hcat [text str, int n]
      | otherwise = hcat [text (trim str), equals, int n, semi]

    trim ls = takeWhile (not . isSpace) (dropWhile isSpace ls)

    (fixity_sigs, bind_tys)
      = count_sigs [d | SigD _ d <- decls]

    val_decls = [d | ValD _ d <- decls]

    real_exports = case exports of { Nothing -> []; Just (L _ es) -> es }
    n_exports = length real_exports
    export_ms = count (\ e -> case unLoc e of
                                IEModuleContents{} -> True
                                _ -> False) real_exports
    export_ds = n_exports - export_ms
    export_all = case exports of { Nothing -> 1; _ -> 0 }

    (fn_bind_ds, ty_bind_ds) = sum2 (map count_bind val_decls)

    (imp_no, imp_qual, imp_as, imp_all, imp_partial, imp_hiding)
      = sum6 (map import_info imports)

    count_bind (FunBind {}) = (1, 0)
    count_bind (TyFunBind {}) = (0, 1)
    count_bind b = pprPanic "count_bind: Unhandled binder" (ppr b)

    count_sigs sigs = sum2 (map sig_info sigs)

    sig_info (FixSig {}) = (1, 0)
    sig_info (TypeSig {}) = (0, 1)
    sig_info _ = (0, 0)

    import_info :: LImportDecl Ps -> (Int, Int, Int, Int, Int, Int)
    import_info (L _ (ImportDecl { ideclQualified = qual, ideclAs = as
                                 , ideclImportList = spec }))
      = add6 (1, qual_info qual, as_info as, 0, 0, 0) (spec_info spec)

    qual_info NotQualified = 0
    qual_info _ = 1

    as_info Nothing = 0
    as_info (Just _) = 1

    spec_info Nothing = (0, 0, 0, 1, 0, 0)
    spec_info (Just (Exactly, _)) = (0, 0, 0, 0, 1, 0)
    spec_info (Just (EverythingBut, _)) = (0, 0, 0, 0, 0, 1)

    sum2 :: [(Int, Int)] -> (Int, Int)
    sum2 = foldr add2 (0, 0)
      where
        add2 (x1, x2) (y1, y2) = (x1+y1, x2+y2)

    add6 :: (Int, Int, Int, Int, Int, Int) -> (Int, Int, Int, Int, Int, Int)
         -> (Int, Int, Int, Int, Int, Int)
    add6 (x1, x2, x3, x4, x5, x6) (y1, y2, y3, y4, y5, y6)
      = (x1+y1, x2+y2, x3+y3, x4+y4, x5+y5, x6+y6)

    sum6 :: [(Int, Int, Int, Int, Int, Int)] -> (Int, Int, Int, Int, Int, Int)
    sum6 = foldr add6 (0, 0, 0, 0, 0, 0)
