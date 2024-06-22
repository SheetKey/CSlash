{-# LANGUAGE LambdaCase #-}

{-# OPTIONS_GHC -Wno-orphans #-} -- instance Outputable CSlashHint

module GHC.Types.Hint.Ppr (
  perhapsAsPat
  -- also, and more interesting: instance Outputable GhcHint
  ) where

import CSlash.Parser.Errors.Basic
import CSlash.Types.Hint

import CSlash.Types.Name
import CSlash.Types.Name.Reader (RdrName,ImpDeclSpec (..), rdrNameOcc, rdrNameSpace)
import CSlash.Types.SrcLoc (SrcSpan(..), srcSpanStartLine)
import CSlash.Unit.Types
import CSlash.Utils.Outputable

import Data.List (intersperse)
import qualified Data.List.NonEmpty as NE

instance Outputable CSlashHint where
  ppr = \case
    UnknownHint m
      -> ppr m
    SuggestUseSpaces
      -> text "Please use spaces instead."
    SuggestUseWhitespaceAfter sym
      -> text "Add whitespace after the"
           <+> quotes (pprOperatorWhitespaceSymbol sym) <> char '.'
    SuggestUseWhitespaceAround sym _occurrence
      -> text "Add whitespace around" <+> quotes (text sym) <> char '.'
    SuggestParentheses
      -> text "Use parentheses."
    SuggestIncreaseMaxPmCheckModels
      -> text "Increase the limit or resolve the warnings to suppress this message."
    SuggestAddTypeSignatures bindings
      -> case bindings of
          UnnamedBinding -> text "Add a type signature."
          NamedBindings (x NE.:| xs) ->
            let nameList = case xs of
                  [] -> quotes . ppr $ x
                  _  -> pprWithCommas (quotes . ppr) xs
                           <+> text "and"
                           <+> quotes (ppr x)
            in hsep [ text "Consider giving"
                    , nameList
                    , text "a type signature"]
    SuggestAddInlineOrNoInlinePragma lhs_id rule_act
      -> vcat [ text "Add an INLINE[n] or NOINLINE[n] pragma for" <+> quotes (ppr lhs_id)
              , whenPprDebug (ppr (idInlineActivation lhs_id) $$ ppr rule_act)
              ]
    SuggestIncreaseSimplifierIterations
      -> text "Set limit with -fconstraint-solver-iterations=n; n=0 for no limit"
    SuggestQualifiedAfterModuleName
      -> text "Place" <+> quotes (text "qualified")
          <+> text "after the module name."
    SuggestFixOrphanInst { isFamilyInstance = mbFamFlavor }
      -> vcat [ text "Move the instance declaration to the module of the" <+> what <+> text "or of the type, or"
              , text "wrap the type with a newtype and declare the instance on the new type."
              ]
      where
        what = case mbFamFlavor of
          Nothing                  -> text "class"
          Just  SynFamilyInst      -> text "type family"
          Just (DataFamilyInst {}) -> text "data family"
    SuggestAddStandaloneKindSignature name
      -> text "Add a standalone kind signature for" <+> quotes (ppr name)
    SuggestMoveToDeclarationSite what rdr_name
      -> text "Move the" <+> what <+> text "to the declaration site of"
         <+> quotes (ppr rdr_name) <> dot
    SuggestSimilarNames tried_rdr_name similar_names
      -> case similar_names of
            n NE.:| [] -> text "Perhaps use" <+> pp_item n
            _          -> sep [ text "Perhaps use one of these:"
                              , nest 2 (pprWithCommas pp_item $ NE.toList similar_names) ]
        where
          tried_ns = occNameSpace $ rdrNameOcc tried_rdr_name
          pp_item = pprSimilarName tried_ns
    ImportSuggestion occ_name import_suggestion
      -> pprImportSuggestion occ_name import_suggestion
    SuggestRenameTypeVariable
      -> text "Consider renaming the type variable."
    SuggestIncreaseReductionDepth ->
      vcat
        [ text "Use -freduction-depth=0 to disable this check"
        , text "(any upper bound you could choose might fail unpredictably with"
        , text " minor updates to CSlash, so disabling the check is recommended if"
        , text " you're sure that type checking should terminate)" ]
    SuggestEtaReduceAbsDataTySyn tc
      -> text "If possible, eta-reduce the type synonym" <+> ppr_tc <+> text "so that it is nullary."
        where ppr_tc = quotes (ppr $ tyConName tc)
    SuggestAnonymousWildcard
      -> text "Use an anonymous wildcard" <+> quotes (text "_")
    SuggestExplicitQuantification tv
      -> hsep [ text "Use an explicit", quotes (text "forall")
              , text "to quantify over", quotes (ppr tv) ]

perhapsAsPat :: SDoc
perhapsAsPat = text "Perhaps you meant an as-pattern, which must not be surrounded by whitespace"

pprImportSuggestion :: OccName -> ImportSuggestion -> SDoc
pprImportSuggestion occ_name (CouldImportFrom mods)
  | (mod, imv) NE.:| [] <- mods
  = fsep
      [ text "Add"
      , quotes (ppr occ_name)
      , text "to the import list"
      , text "in the import of"
      , quotes (ppr mod)
      , parens (text "at" <+> ppr (imv_span imv)) <> dot
      ]
  | otherwise
  = fsep
      [ text "Add"
      , quotes (ppr occ_name)
      , text "to one of these import lists:"
      ]
    $$
    nest 2 (vcat
        [ quotes (ppr mod) <+> parens (text "at" <+> ppr (imv_span imv))
        | (mod,imv) <- NE.toList mods
        ])
pprImportSuggestion occ_name (CouldUnhideFrom mods)
  | (mod, imv) NE.:| [] <- mods
  = fsep
      [ text "Remove"
      , quotes (ppr occ_name)
      , text "from the explicit hiding list"
      , text "in the import of"
      , quotes (ppr mod)
      , parens (text "at" <+> ppr (imv_span imv)) <> dot
      ]
  | otherwise
  = fsep
      [ text "Remove"
      , quotes (ppr occ_name)
      , text "from the hiding clauses"
      , text "in one of these imports:"
      ]
    $$
    nest 2 (vcat
        [ quotes (ppr mod) <+> parens (text "at" <+> ppr (imv_span imv))
        | (mod,imv) <- NE.toList mods
        ])
pprImportSuggestion occ_name (CouldAddTypeKeyword mod)
  = vcat [ text "Add the" <+> quotes (text "type")
          <+> text "keyword to the import statement:"
         , nest 2 $ text "import"
            <+> ppr mod
            <+> parens_sp (text "type" <+> pprPrefixOcc occ_name)
         ]
  where
    parens_sp d = parens (space <> d <> space)
pprImportSuggestion occ_name (CouldRemoveTypeKeyword mod)
  = vcat [ text "Remove the" <+> quotes (text "type")
             <+> text "keyword from the import statement:"
         , nest 2 $ text "import"
             <+> ppr mod
             <+> parens_sp (pprPrefixOcc occ_name) ]
  where
    parens_sp d = parens (space <> d <> space)
pprImportSuggestion dc_occ (ImportDataCon Nothing parent_occ)
  = text "Import the data constructor" <+> quotes (ppr dc_occ) <+>
    text "of" <+> quotes (ppr parent_occ)
pprImportSuggestion dc_occ (ImportDataCon (Just (mod, patsyns_enabled)) parent_occ)
  = vcat $ [ text "Use"
           , nest 2 $ text "import"
               <+> ppr mod
               <+> parens_sp (pprPrefixOcc parent_occ <> parens_sp (pprPrefixOcc dc_occ))
           , text "or"
           , nest 2 $ text "import"
               <+> ppr mod
               <+> parens_sp (pprPrefixOcc parent_occ <> text "(..)")
           ] ++ if patsyns_enabled
                then [ text "or"
                     , nest 2 $ text "import"
                         <+> ppr mod
                         <+> parens_sp (text "pattern" <+> pprPrefixOcc dc_occ)
                     ]
                else []
  where
    parens_sp d = parens (space <> d <> space)

pprSimilarName :: NameSpace -> SimilarName -> SDoc
pprSimilarName _ (SimilarName name)
  = quotes (ppr name) <+> parens (pprDefinedAt name)
pprSimilarName tried_ns (SimilarRdrName rdr_name how_in_scope)
  = pp_ns rdr_name <+> quotes (ppr rdr_name) <+> loc
  where
    loc = case how_in_scope of
      Nothing -> empty
      Just scope -> case scope of
        LocallyBoundAt loc ->
          case loc of
            UnhelpfulSpan l -> parens (ppr l)
            RealSrcSpan l _ -> parens (text "line" <+> int (srcSpanStartLine l))
        ImportedBy is ->
          parens (text "imported from" <+> ppr (moduleName $ is_mod is))
    pp_ns :: RdrName -> SDoc
    pp_ns rdr | ns /= tried_ns = pprNameSpace ns
              | otherwise      = empty
      where ns = rdrNameSpace rdr

pprPrefixUnqual :: Name -> SDoc
pprPrefixUnqual name =
  pprPrefixOcc (getOccName name)
