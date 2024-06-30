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

import CSlash.Data.FastString (FastString, mkFastString, unpackFS)
import CSlash.Types.SourceText
import CSlash.Types.Name.Occurrence
import CSlash.Types.Name.Env
import CSlash.Types.Name (Name)
import CSlash.Types.SrcLoc
import CSlash.Types.Unique
import CSlash.Types.Unique.Set
import CSlash.Cs.Doc
import CSlash.Cs.Extension
import CSlash.Parser.Annotation

import CSlash.Utils.Outputable
import CSlash.Utils.Binary
import CSlash.Unicode

import CSlash.Language.Syntax.Extension

import Data.Data
import Data.List (isPrefixOf)
import GHC.Generics ( Generic )
import Control.DeepSeq

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

data WarningCategorySet
  = FiniteWarningCategorySet   (UniqSet WarningCategory)
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
      [LocatedE (WithCsDocIdentifiers StringLiteral pass)]
   | DeprecatedTxt
      SourceText
      [LocatedE (WithCsDocIdentifiers StringLiteral pass)]
  deriving Generic

warningTxtCategory :: WarningTxt pass -> WarningCategory
warningTxtCategory (WarningTxt (Just (L _ (InWarningCategory _  _ (L _ cat)))) _ _) = cat
warningTxtCategory _ = defaultWarningCategory

warningTxtMessage :: WarningTxt p -> [LocatedE (WithCsDocIdentifiers StringLiteral p)]
warningTxtMessage (WarningTxt _ _ m) = m
warningTxtMessage (DeprecatedTxt _ m) = m

warningTxtSame :: WarningTxt p1 -> WarningTxt p2 -> Bool
warningTxtSame w1 w2
  = warningTxtCategory w1 == warningTxtCategory w2
  && literal_message w1 == literal_message w2
  && same_type
  where
    literal_message :: WarningTxt p -> [StringLiteral]
    literal_message = map (csDocString . unLoc) . warningTxtMessage
    same_type | DeprecatedTxt {} <- w1, DeprecatedTxt {} <- w2 = True
              | WarningTxt {} <- w1, WarningTxt {} <- w2       = True
              | otherwise                                      = False

deriving instance Eq InWarningCategory

deriving instance (Eq (IdP pass)) => Eq (WarningTxt pass)
deriving instance (Data pass, Data (IdP pass)) => Data (WarningTxt pass)

type instance Anno (WarningTxt (CsPass pass)) = SrcSpanAnnP

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

pp_ws :: [LocatedE (WithCsDocIdentifiers StringLiteral pass)] -> SDoc
pp_ws [l] = ppr $ unLoc l
pp_ws ws
  = text "["
    <+> vcat (punctuate comma (map (ppr . unLoc) ws))
    <+> text "]"


pprWarningTxtForMsg :: WarningTxt p -> SDoc
pprWarningTxtForMsg (WarningTxt _ _ ws)
                     = doubleQuotes (vcat (map (ftext . sl_fs . csDocString . unLoc) ws))
pprWarningTxtForMsg (DeprecatedTxt _ ds)
                     = text "Deprecated:" <+>
                       doubleQuotes (vcat (map (ftext . sl_fs . csDocString . unLoc) ds))

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
