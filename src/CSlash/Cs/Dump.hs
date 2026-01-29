{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CSlash.Cs.Dump where

import Prelude hiding ((<>))

import CSlash.Cs

import CSlash.Core.DataCon

import CSlash.Data.Bag
import CSlash.Data.FastString
import CSlash.Types.Name.Set
import CSlash.Types.Name
import CSlash.Types.SrcLoc
import CSlash.Types.Var
import CSlash.Types.SourceText
import CSlash.Utils.Outputable

import Data.Data hiding (Fixity)
import qualified Data.ByteString as B

data BlankSrcSpan = BlankSrcSpan | BlankSrcSpanFile | NoBlankSrcSpan
  deriving (Eq, Show)

data BlankEpAnnotations = BlankEpAnnotations | NoBlankEpAnnotations
  deriving (Eq, Show)

showAstDataFull :: Data a => a -> SDoc
showAstDataFull = showAstData NoBlankSrcSpan NoBlankEpAnnotations

showAstData :: Data a => BlankSrcSpan -> BlankEpAnnotations -> a -> SDoc
showAstData bs ba a0 = blankLine $$ showAstData' a0
  where
    showAstData' :: Data a => a -> SDoc
    showAstData' =
      generic `ext1Q` list
              `extQ` list_addEpAnn
              `extQ` string `extQ` fastString `extQ` srcSpan `extQ` realSrcSpan
              `extQ` annotation
              `extQ` annotationModule
              `extQ` annotationAddEpAnn
              `extQ` annotationGrhsAnn
              `extQ` annotationEpAnnCsCase
              `extQ` annotationAnnList
              `extQ` annotationEpAnnImportDecl
              `extQ` annotationAnnParen
              `extQ` annotationTrailingAnn
              `extQ` annotationEpaLocation
              `extQ` annotationNoEpAnns
              `extQ` addEpAnn
              `extQ` annParen
              `extQ` lit `extQ` litr `extQ` litt
              `extQ` sourceText
              `extQ` deltaPos
              `extQ` epaAnchor
              `extQ` bytestring
              `extQ` name `extQ` occName `extQ` moduleName `extQ` var
              `extQ` dataCon
              `extQ` bagName `extQ` bagRdrName `extQ` bagVar `extQ` nameSet
              `extQ` fixity
              `ext2Q` located
              `extQ` srcSpanAnnA
              `extQ` srcSpanAnnL
              `extQ` srcSpanAnnP
              `extQ` srcSpanAnnC
              `extQ` srcSpanAnnN
      where
        generic :: Data a => a -> SDoc
        generic t = parens $ text (showConstr (toConstr t))
                    $$ vcat (gmapQ showAstData' t)

        string :: String -> SDoc
        string = text . normalize_newlines . show

        fastString :: FastString -> SDoc
        fastString s = braces $
                       text "FastString:"
                       <+> text (normalize_newlines . show $ s)

        bytestring :: B.ByteString -> SDoc
        bytestring = text . normalize_newlines . show

        list_addEpAnn :: [AddEpAnn] -> SDoc
        list_addEpAnn ls = case ba of
          BlankEpAnnotations -> parens $ text "blanked:" <+> text "[AddEpAnn]"
          NoBlankEpAnnotations -> list ls

        list [] = brackets empty
        list [x] = brackets (showAstData' x)
        list (x1 : x2 : xs) = (text "[" <> showAstData' x1) $$ go x2 xs
          where
            go y [] = text "," <> showAstData' y <> text "]"
            go y1 (y2 : ys) = (text "," <> showAstData' y1) $$ go y2 ys

        lit :: CsLit Ps -> SDoc
        lit l = generic l

        litr :: CsLit Ps -> SDoc
        litr l = generic l

        litt :: CsLit Ps -> SDoc
        litt l = generic l

        sourceText :: SourceText -> SDoc
        sourceText NoSourceText = parens $ text "NoSourceText"
        sourceText (SourceText src) = case bs of
          NoBlankSrcSpan -> parens $ text "SourceText" <+> ftext src
          BlankSrcSpanFile -> parens $ text "SourceText" <+> ftext src
          _ -> parens $ text "SourceText" <+> text "blanked"

        epaAnchor :: EpaLocation -> SDoc
        epaAnchor (EpaSpan s) = parens $ text "EpaSpan" <+> srcSpan s
        epaAnchor (EpaDelta d cs) = case ba of
          NoBlankEpAnnotations -> parens $ text "EpaDelta" <+> deltaPos d <+> showAstData' cs
          BlankEpAnnotations -> parens $ text "EpaDelta" <+> deltaPos d <+> text "blanked"

        deltaPos :: DeltaPos -> SDoc
        deltaPos (SameLine c) = parens $ text "SameLine" <+> ppr c
        deltaPos (DifferentLine l c) = parens $ text "DifferentLine" <+> ppr l <+> ppr c

        name :: Name -> SDoc
        name nm = braces $ text "Name:" <+> ppr nm

        occName n = braces $ text "OccName:" <+> ftext (occNameFS n)

        moduleName :: ModuleName -> SDoc
        moduleName m = braces $ text "ModuleName:" <+> ppr m

        srcSpan :: SrcSpan -> SDoc
        srcSpan ss = case bs of
          BlankSrcSpan -> text "{ ss }"
          NoBlankSrcSpan -> braces $ char ' ' <> (ppr ss) <> char ' '
          BlankSrcSpanFile -> braces $ char ' ' <> (pprUserSpan False ss) <> char ' '

        realSrcSpan :: RealSrcSpan -> SDoc
        realSrcSpan ss = case bs of
          BlankSrcSpan -> text "{ ss }"
          NoBlankSrcSpan -> braces $ char ' ' <> (ppr ss) <> char ' '
          BlankSrcSpanFile -> braces $ char ' ' <> (pprUserRealSpan False ss) <> char ' '

        annParen :: AnnParen -> SDoc
        annParen (AnnParen a o c) = case ba of
          BlankEpAnnotations -> parens $ text "blanked:" <+> text "AnnParen"
          NoBlankEpAnnotations -> parens $ text "AnnParen" $$
                                  vcat [ppr a, epaAnchor o, epaAnchor c]

        addEpAnn :: AddEpAnn -> SDoc
        addEpAnn (AddEpAnn a s) = case ba of
          BlankEpAnnotations -> parens $ text "blanked:" <+> text "AddEpAnn"
          NoBlankEpAnnotations -> parens $ text "AddEpAnn" <+> ppr a <+> epaAnchor s

        var :: Id Zk -> SDoc
        var v = braces $ text "Var:" <+> ppr v

        dataCon :: DataCon Zk -> SDoc
        dataCon c = braces $ text "DataCon:" <+> ppr c

        bagRdrName :: Bag (LocatedA (CsBind Ps)) -> SDoc
        bagRdrName bg = braces $
                        text "Bag(LocatedA (CsBind Ps)):"
                        $$ (list . bagToList $ bg)

        bagName :: Bag (LocatedA (CsBind Rn)) -> SDoc
        bagName bg = braces $
                     text "Bag(LocatedA (CsBind Name)):"
                     $$ (list . bagToList $ bg)

        bagVar :: Bag (LocatedA (CsBind Tc)) -> SDoc
        bagVar bg = braces $
                    text "Bag(LocatedA (CsBind Var)):"
                    $$ (list . bagToList $ bg)

        nameSet ns = braces $
                     text "NameSet:"
                     $$ (list . nameSetElemsStable $ ns)

        fixity :: Fixity -> SDoc
        fixity fx = braces $
                    text "Fixity:"
                    <+> ppr fx

        located :: (Data a, Data b) => GenLocated a b -> SDoc
        located (L ss a)
          = parens (text "L"
                    $$ vcat [showAstData' ss, showAstData' a])

        -- -------------------------

        annotation :: EpAnn [AddEpAnn] -> SDoc
        annotation = annotation' (text "EpAnn [AddEpAnn]")

        annotationModule :: EpAnn AnnsModule -> SDoc
        annotationModule = annotation' (text "EpAnn AnnsModule")

        annotationAddEpAnn :: EpAnn AddEpAnn -> SDoc
        annotationAddEpAnn = annotation' (text "EpAnn AddEpAnn")

        annotationGrhsAnn :: EpAnn [AddEpAnn] -> SDoc
        annotationGrhsAnn = annotation' (text "EpAnn GrhsAnn")

        annotationEpAnnCsCase :: EpAnn [AddEpAnn] -> SDoc
        annotationEpAnnCsCase = annotation' (text "EpAnn EpAnnCsCase")

        annotationAnnList :: EpAnn [AddEpAnn] -> SDoc
        annotationAnnList = annotation' (text "EpAnn AnnList")

        annotationEpAnnImportDecl :: EpAnn [AddEpAnn] -> SDoc
        annotationEpAnnImportDecl = annotation' (text "EpAnn EpAnnImportDecl")

        annotationAnnParen :: EpAnn [AddEpAnn] -> SDoc
        annotationAnnParen = annotation' (text "EpAnn AnnParen")

        annotationTrailingAnn :: EpAnn [AddEpAnn] -> SDoc
        annotationTrailingAnn = annotation' (text "EpAnn TrailingAnn")

        annotationEpaLocation :: EpAnn [AddEpAnn] -> SDoc
        annotationEpaLocation = annotation' (text "EpAnn EpaLocation")

        annotationNoEpAnns :: EpAnn [AddEpAnn] -> SDoc
        annotationNoEpAnns = annotation' (text "EpAnn NoEpAnns")

        annotation'
          :: forall a. (Data a, Typeable a)
          => SDoc -> EpAnn a -> SDoc
        annotation' tag anns = case ba of
          BlankEpAnnotations -> parens (text "blanked:" <+> tag)
          NoBlankEpAnnotations -> parens $ text (showConstr (toConstr anns))
                                  $$ vcat (gmapQ showAstData' anns)

        -- -------------------------
        
        srcSpanAnnA :: EpAnn AnnListItem -> SDoc
        srcSpanAnnA = locatedAnn'' (text "SrcSpanAnnA")

        srcSpanAnnL :: EpAnn AnnListItem -> SDoc
        srcSpanAnnL = locatedAnn'' (text "SrcSpanAnnL")

        srcSpanAnnP :: EpAnn AnnListItem -> SDoc
        srcSpanAnnP = locatedAnn'' (text "SrcSpanAnnP")

        srcSpanAnnC :: EpAnn AnnListItem -> SDoc
        srcSpanAnnC = locatedAnn'' (text "SrcSpanAnnC")

        srcSpanAnnN :: EpAnn AnnListItem -> SDoc
        srcSpanAnnN = locatedAnn'' (text "SrcSpanAnnN")

        locatedAnn''
          :: forall a. (Data a, Typeable a)
          => SDoc -> EpAnn a -> SDoc
        locatedAnn'' tag ss = parens $
          case cast ss of
            Just (ann :: EpAnn a) ->
              case ba of
                BlankEpAnnotations -> parens (text "blanked:" <+> tag)
                NoBlankEpAnnotations -> text (showConstr (toConstr ann))
                                        $$ vcat (gmapQ showAstData' ann)
            Nothing -> text "locatedAnn:unmatched" <+> tag
                       <+> (parens $ text (showConstr (toConstr ss)))

normalize_newlines :: String -> String
normalize_newlines ('\\':'r':'\\':'n':xs) = '\\':'n':normalize_newlines xs
normalize_newlines (x:xs) = x:normalize_newlines xs
normalize_newlines [] = []

newtype Q q x = Q { unQ :: x -> q }

extQ
  :: (Typeable a, Typeable b)
  => (a -> q) -> (b -> q) -> a -> q
extQ f g a = maybe (f a) g (cast a)

ext1Q
  :: (Data d, Typeable t)
  => (d -> q) -> (forall e. Data e => t e -> q) -> d -> q
ext1Q def ext = unQ ((Q def) `ext1` (Q ext))

ext2Q
  :: (Data d, Typeable t)
  => (d -> q) -> (forall d1 d2. (Data d1, Data d2) => t d1 d2 -> q) -> d -> q
ext2Q def ext = unQ ((Q def) `ext2` (Q ext))

ext1
  :: (Data a, Typeable t)
  => c a -> (forall d. Data d => c (t d)) -> c a
ext1 def ext = maybe def id (dataCast1 ext)

ext2
  :: (Data a, Typeable t)
  => c a -> (forall d1 d2. (Data d1, Data d2) => c (t d1 d2)) -> c a
ext2 def ext = maybe def id (dataCast2 ext)
