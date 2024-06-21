{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module CSlash.Unit.Module.Warnings
   ( WarningCategory(..)
   , mkWarningCategory
   , defaultWarningCategory
   , validWarningCategory
   , InWarningCategory(..)
   , fromWarningCategory

   , WarningCategorySet
   , emptyWarningCategorySet
   , completeWarningCategorySet
   , nullWarningCategorySet
   , elemWarningCategorySet
   , insertWarningCategorySet
   , deleteWarningCategorySet

   , Warnings (..)
   , WarningTxt (..)
   , LWarningTxt
   , DeclWarnOccNames
   , ExportWarnNames
   , warningTxtCategory
   , warningTxtMessage
   , warningTxtSame
   , pprWarningTxtForMsg
   , emptyWarn
   , mkIfaceDeclWarnCache
   , mkIfaceExportWarnCache
   , emptyIfaceWarnCache
   , insertWarnDecls
   , insertWarnExports
   )
where

import GHC.Prelude

import GHC.Data.FastString (FastString, mkFastString, unpackFS)
import GHC.Types.SourceText
import GHC.Types.Name.Occurrence
import GHC.Types.Name.Env
import GHC.Types.Name (Name)
import GHC.Types.SrcLoc
import GHC.Types.Unique
import GHC.Types.Unique.Set
import GHC.Hs.Doc
import GHC.Hs.Extension
import GHC.Parser.Annotation

import GHC.Utils.Outputable
import GHC.Utils.Binary
import GHC.Unicode

import Language.Haskell.Syntax.Extension

import Data.Data
import Data.List (isPrefixOf)
import GHC.Generics ( Generic )
import Control.DeepSeq


{-
Note [Warning categories]
~~~~~~~~~~~~~~~~~~~~~~~~~
See GHC Proposal 541 for the design of the warning categories feature:
https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0541-warning-pragmas-with-categories.rst

A WARNING pragma may be annotated with a category such as "x-partial" written
after the 'in' keyword, like this:

    {-# WARNING in "x-partial" head "This function is partial..." #-}

This is represented by the 'Maybe (Located WarningCategory)' field in
'WarningTxt'.  The parser will accept an arbitrary string as the category name,
then the renamer (in 'rnWarningTxt') will check it contains only valid
characters, so we can generate a nicer error message than a parse error.

The corresponding warnings can then be controlled with the -Wx-partial,
-Wno-x-partial, -Werror=x-partial and -Wwarn=x-partial flags.  Such a flag is
distinguished from an 'unrecognisedWarning' by the flag parser testing
'validWarningCategory'.  The 'x-' prefix means we can still usually report an
unrecognised warning where the user has made a mistake.

A DEPRECATED pragma may not have a user-defined category, and is always treated
as belonging to the special category 'deprecations'.  Similarly, a WARNING
pragma without a category belongs to the 'deprecations' category.
Thus the '-Wdeprecations' flag will enable all of the following:

    {-# WARNING in "deprecations" foo "This function is deprecated..." #-}
    {-# WARNING foo "This function is deprecated..." #-}
    {-# DEPRECATED foo "This function is deprecated..." #-}

The '-Wwarnings-deprecations' flag is supported for backwards compatibility
purposes as being equivalent to '-Wdeprecations'.

The '-Wextended-warnings' warning group collects together all warnings with
user-defined categories, so they can be enabled or disabled
collectively. Moreover they are treated as being part of other warning groups
such as '-Wdefault' (see 'warningGroupIncludesExtendedWarnings').

'DynFlags' and 'DiagOpts' each contain a set of enabled and a set of fatal
warning categories, just as they do for the finite enumeration of 'WarningFlag's
built in to GHC.  These are represented as 'WarningCategorySet's to allow for
the possibility of them being infinite.

-}

data InWarningCategory
  = InWarningCategory
    { iwc_in :: !(EpToken "in"),
      iwc_st :: !SourceText,
      iwc_wc :: (LocatedE WarningCategory)
    } deriving Data

fromWarningCategory :: WarningCategory -> InWarningCategory
fromWarningCategory wc = InWarningCategory noAnn NoSourceText (noLocA wc)

newtype WarningCategory = WarningCategory FastString
  deriving (Binary, Data, Eq, Outputable, Show, Uniquable, NFData)

mkWarningCategory :: FastString -> WarningCategory
mkWarningCategory = WarningCategory

defaultWarningCategory :: WarningCategory
defaultWarningCategory = mkWarningCategory (mkFastString "deprecations")

validWarningCategory :: WarningCategory -> Bool
validWarningCategory cat@(WarningCategory c) =
    cat == defaultWarningCategory || ("x-" `isPrefixOf` s && all is_allowed s)
  where
    s = unpackFS c
    is_allowed c = isAlphaNum c || c == '\'' || c == '-'


data WarningCategorySet =
    FiniteWarningCategorySet   (UniqSet WarningCategory)
  | CofiniteWarningCategorySet (UniqSet WarningCategory)

emptyWarningCategorySet :: WarningCategorySet
emptyWarningCategorySet = FiniteWarningCategorySet emptyUniqSet

completeWarningCategorySet :: WarningCategorySet
completeWarningCategorySet = CofiniteWarningCategorySet emptyUniqSet

nullWarningCategorySet :: WarningCategorySet -> Bool
nullWarningCategorySet (FiniteWarningCategorySet s) = isEmptyUniqSet s
nullWarningCategorySet CofiniteWarningCategorySet{} = False

elemWarningCategorySet :: WarningCategory -> WarningCategorySet -> Bool
elemWarningCategorySet c (FiniteWarningCategorySet   s) =      c `elementOfUniqSet` s
elemWarningCategorySet c (CofiniteWarningCategorySet s) = not (c `elementOfUniqSet` s)

insertWarningCategorySet :: WarningCategory -> WarningCategorySet -> WarningCategorySet
insertWarningCategorySet c (FiniteWarningCategorySet   s) = FiniteWarningCategorySet   (addOneToUniqSet   s c)
insertWarningCategorySet c (CofiniteWarningCategorySet s) = CofiniteWarningCategorySet (delOneFromUniqSet s c)

deleteWarningCategorySet :: WarningCategory -> WarningCategorySet -> WarningCategorySet
deleteWarningCategorySet c (FiniteWarningCategorySet   s) = FiniteWarningCategorySet   (delOneFromUniqSet s c)
deleteWarningCategorySet c (CofiniteWarningCategorySet s) = CofiniteWarningCategorySet (addOneToUniqSet   s c)

type LWarningTxt pass = XRec pass (WarningTxt pass)

data WarningTxt pass
   = WarningTxt
      (Maybe (LocatedE InWarningCategory))
      SourceText
      [LocatedE (WithHsDocIdentifiers StringLiteral pass)]
   | DeprecatedTxt
      SourceText
      [LocatedE (WithHsDocIdentifiers StringLiteral pass)]
  deriving Generic

warningTxtCategory :: WarningTxt pass -> WarningCategory
warningTxtCategory (WarningTxt (Just (L _ (InWarningCategory _  _ (L _ cat)))) _ _) = cat
warningTxtCategory _ = defaultWarningCategory

warningTxtMessage :: WarningTxt p -> [LocatedE (WithHsDocIdentifiers StringLiteral p)]
warningTxtMessage (WarningTxt _ _ m) = m
warningTxtMessage (DeprecatedTxt _ m) = m

warningTxtSame :: WarningTxt p1 -> WarningTxt p2 -> Bool
warningTxtSame w1 w2
  = warningTxtCategory w1 == warningTxtCategory w2
  && literal_message w1 == literal_message w2
  && same_type
  where
    literal_message :: WarningTxt p -> [StringLiteral]
    literal_message = map (hsDocString . unLoc) . warningTxtMessage
    same_type | DeprecatedTxt {} <- w1, DeprecatedTxt {} <- w2 = True
              | WarningTxt {} <- w1, WarningTxt {} <- w2       = True
              | otherwise                                      = False

deriving instance Eq InWarningCategory

deriving instance (Eq (IdP pass)) => Eq (WarningTxt pass)
deriving instance (Data pass, Data (IdP pass)) => Data (WarningTxt pass)

type instance Anno (WarningTxt (GhcPass pass)) = SrcSpanAnnP

instance Outputable InWarningCategory where
  ppr (InWarningCategory _ _ wt) = text "in" <+> doubleQuotes (ppr wt)


instance Outputable (WarningTxt pass) where
    ppr (WarningTxt mcat lsrc ws)
      = case lsrc of
            NoSourceText   -> pp_ws ws
            SourceText src -> ftext src <+> ctg_doc <+> pp_ws ws <+> text "#-}"
        where
          ctg_doc = maybe empty (\ctg -> ppr ctg) mcat


    ppr (DeprecatedTxt lsrc  ds)
      = case lsrc of
          NoSourceText   -> pp_ws ds
          SourceText src -> ftext src <+> pp_ws ds <+> text "#-}"

pp_ws :: [LocatedE (WithHsDocIdentifiers StringLiteral pass)] -> SDoc
pp_ws [l] = ppr $ unLoc l
pp_ws ws
  = text "["
    <+> vcat (punctuate comma (map (ppr . unLoc) ws))
    <+> text "]"


pprWarningTxtForMsg :: WarningTxt p -> SDoc
pprWarningTxtForMsg (WarningTxt _ _ ws)
                     = doubleQuotes (vcat (map (ftext . sl_fs . hsDocString . unLoc) ws))
pprWarningTxtForMsg (DeprecatedTxt _ ds)
                     = text "Deprecated:" <+>
                       doubleQuotes (vcat (map (ftext . sl_fs . hsDocString . unLoc) ds))

data Warnings pass
  = WarnSome (DeclWarnOccNames pass) 
             (ExportWarnNames pass)  
  | WarnAll (WarningTxt pass)        

type DeclWarnOccNames pass = [(OccName, WarningTxt pass)]

type ExportWarnNames pass = [(Name, WarningTxt pass)]

deriving instance Eq (IdP pass) => Eq (Warnings pass)

emptyWarn :: Warnings p
emptyWarn = WarnSome [] []

mkIfaceDeclWarnCache :: Warnings p -> OccName -> Maybe (WarningTxt p)
mkIfaceDeclWarnCache (WarnAll t) = \_ -> Just t
mkIfaceDeclWarnCache (WarnSome vs _) = lookupOccEnv (mkOccEnv vs)

mkIfaceExportWarnCache :: Warnings p -> Name -> Maybe (WarningTxt p)
mkIfaceExportWarnCache (WarnAll _) = const Nothing 
mkIfaceExportWarnCache (WarnSome _ ds) = lookupNameEnv (mkNameEnv ds)

emptyIfaceWarnCache :: name -> Maybe (WarningTxt p)
emptyIfaceWarnCache _ = Nothing

insertWarnDecls :: Warnings p                
                -> [(OccName, WarningTxt p)] 
                -> Warnings p                
insertWarnDecls ws@(WarnAll _) _        = ws
insertWarnDecls (WarnSome wns wes) wns' = WarnSome (wns ++ wns') wes

insertWarnExports :: Warnings p             
                  -> [(Name, WarningTxt p)] 
                  -> Warnings p             
insertWarnExports ws@(WarnAll _) _ = ws
insertWarnExports (WarnSome wns wes) wes' = WarnSome wns (wes ++ wes')
