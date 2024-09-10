{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module CSlash.Types.Error.Codes
  ( CsDiagnosticCode, constructorCode, constructorCodes
  ) where

import CSlash.Types.Error
  ( DiagnosticCode(..), UnknownDiagnostic (..), diagnosticCode, NoDiagnosticOpts )

import CSlash.Cs.Extension ( Rn )

-- import GHC.Core.InstEnv (LookupInstanceErrReason)
-- import GHC.Iface.Errors.Types
import CSlash.Driver.Errors.Types   ( DriverMessage, CsMessageOpts, DriverMessageOpts )
import CSlash.Parser.Errors.Types   ( PsMessage{-, PsHeaderMessage-} )
-- import GHC.HsToCore.Errors.Types ( DsMessage )
-- import GHC.Tc.Errors.Types
import CSlash.Unit.Module.Warnings ( WarningTxt )
import CSlash.Utils.Panic.Plain

import Data.Kind    ( Type, Constraint )
import GHC.Exts     ( proxy# )
import GHC.Generics
import GHC.TypeLits ( Symbol, KnownSymbol, symbolVal'
                    , TypeError, ErrorMessage(..) )
import GHC.TypeNats ( Nat, KnownNat, natVal' )

import Data.Map.Strict ( Map )
import qualified Data.Map.Strict as Map

{- *********************************************************************
*                                                                      *
                 The CsDiagnosticCode type family
*                                                                      *
********************************************************************* -}

constructorCode :: (Generic diag, GDiagnosticCode (Rep diag))
                => diag -> Maybe DiagnosticCode
constructorCode diag = gdiagnosticCode (from diag)

constructorCodes :: forall diag. (Generic diag, GDiagnosticCodes '[diag] (Rep diag))
                 => Map DiagnosticCode String
constructorCodes = gdiagnosticCodes @'[diag] @(Rep diag)

type CsDiagnosticCode :: Symbol -> Nat
type family CsDiagnosticCode c = n | n -> c where
  -- Parser diagnostic codes
  -- CsDiagnosticCode "PsErrParseLanguagePragma"                      = 68686
  -- CsDiagnosticCode "PsErrUnsupportedExt"                           = 46537
  -- CsDiagnosticCode "PsErrParseOptionsPragma"                       = 24342
  -- CsDiagnosticCode "PsErrUnknownOptionsPragma"                     = 04924
  CsDiagnosticCode "PsWarnBidirectionalFormatChars"                = 03272
  CsDiagnosticCode "PsWarnTab"                                     = 94817
  -- CsDiagnosticCode "PsWarnTransitionalLayout"                      = 93617
  -- CsDiagnosticCode "PsWarnOperatorWhitespaceExtConflict"           = 47082
  CsDiagnosticCode "PsWarnOperatorWhitespace"                      = 40798
  -- CsDiagnosticCode "PsWarnHaddockInvalidPos"                       = 94458
  -- CsDiagnosticCode "PsWarnHaddockIgnoreMulti"                      = 05641
  -- CsDiagnosticCode "PsWarnStarBinder"                              = 21887
  -- CsDiagnosticCode "PsWarnStarIsType"                              = 39567
  -- CsDiagnosticCode "PsWarnUnrecognisedPragma"                      = 42044
  -- CsDiagnosticCode "PsWarnMisplacedPragma"                         = 28007
  CsDiagnosticCode "PsErrImportPreQualified"                          = 07924
  CsDiagnosticCode "PsErrLexer"                                    = 21231
  -- CsDiagnosticCode "PsErrCmmLexer"                                 = 75725
  -- CsDiagnosticCode "PsErrCmmParser"                                = 09848
  CsDiagnosticCode "PsErrParse"                                    = 58481
  -- CsDiagnosticCode "PsErrTypeAppWithoutSpace"                      = 84077
  -- CsDiagnosticCode "PsErrLazyPatWithoutSpace"                      = 27207
  -- CsDiagnosticCode "PsErrBangPatWithoutSpace"                      = 95644
  CsDiagnosticCode "PsErrInvalidInfixHole"                         = 45106
  -- CsDiagnosticCode "PsErrExpectedHyphen"                           = 44524
  -- CsDiagnosticCode "PsErrSpaceInSCC"                               = 76176
  -- CsDiagnosticCode "PsErrEmptyDoubleQuotes"                        = 11861
  -- CsDiagnosticCode "PsErrLambdaCase"                               = 51179
  CsDiagnosticCode "PsErrEmptyLambda"                              = 71614
  -- CsDiagnosticCode "PsErrLinearFunction"                           = 31574
  CsDiagnosticCode "PsErrMultiWayIf"                               = 28985
  -- CsDiagnosticCode "PsErrOverloadedRecordUpdateNotEnabled"         = 82135
  -- CsDiagnosticCode "PsErrNumUnderscores"                           = 62330
  -- CsDiagnosticCode "PsErrIllegalBangPattern"                       = 79767
  -- CsDiagnosticCode "PsErrOverloadedRecordDotInvalid"               = 26832
  -- CsDiagnosticCode "PsErrIllegalPatSynExport"                      = 89515
  -- CsDiagnosticCode "PsErrOverloadedRecordUpdateNoQualifiedFields"  = 94863
  -- CsDiagnosticCode "PsErrExplicitForall"                           = 25955
  -- CsDiagnosticCode "PsErrIllegalQualifiedDo"                       = 40280
  -- CsDiagnosticCode "PsErrQualifiedDoInCmd"                         = 54089
  -- CsDiagnosticCode "PsErrRecordSyntaxInPatSynDecl"                 = 28021
  -- CsDiagnosticCode "PsErrEmptyWhereInPatSynDecl"                   = 13248
  -- CsDiagnosticCode "PsErrInvalidWhereBindInPatSynDecl"             = 24737
  -- CsDiagnosticCode "PsErrNoSingleWhereBindInPatSynDecl"            = 65536
  -- CsDiagnosticCode "PsErrDeclSpliceNotAtTopLevel"                  = 08451
  -- CsDiagnosticCode "PsErrMultipleNamesInStandaloneKindSignature"   = 42569
  -- CsDiagnosticCode "PsErrIllegalExplicitNamespace"                 = 47007
  -- CsDiagnosticCode "PsErrUnallowedPragma"                          = 85314
  -- CsDiagnosticCode "PsErrImportPostQualified"                      = 87491
  CsDiagnosticCode "PsErrImportQualifiedTwice"                     = 05661
  -- CsDiagnosticCode "PsErrIllegalImportBundleForm"                  = 81284
  -- CsDiagnosticCode "PsErrInvalidRuleActivationMarker"              = 50396
  CsDiagnosticCode "PsErrMissingBlock"                             = 16849
  -- CsDiagnosticCode "PsErrUnsupportedBoxedSumExpr"                  = 09550
  -- CsDiagnosticCode "PsErrUnsupportedBoxedSumPat"                   = 16863
  CsDiagnosticCode "PsErrUnexpectedQualifiedConstructor"           = 73413
  CsDiagnosticCode "PsErrTupleSectionInPat"                        = 09646
  CsDiagnosticCode "PsErrOpFewArgs"                                = 24180
  CsDiagnosticCode "PsErrVarForTyCon"                              = 18208
  -- CsDiagnosticCode "PsErrMalformedEntityString"                    = 26204
  -- CsDiagnosticCode "PsErrDotsInRecordUpdate"                       = 70712
  -- CsDiagnosticCode "PsErrInvalidDataCon"                           = 46574
  -- CsDiagnosticCode "PsErrInvalidInfixDataCon"                      = 30670
  -- CsDiagnosticCode "PsErrIllegalPromotionQuoteDataCon"             = 80236
  -- CsDiagnosticCode "PsErrUnpackDataCon"                            = 40845
  -- CsDiagnosticCode "PsErrUnexpectedKindAppInDataCon"               = 83653
  -- CsDiagnosticCode "PsErrInvalidRecordCon"                         = 08195
  -- CsDiagnosticCode "PsErrIllegalUnboxedStringInPat"                = 69925
  -- CsDiagnosticCode "PsErrIllegalUnboxedFloatingLitInPat"           = 76595
  -- CsDiagnosticCode "PsErrDoNotationInPat"                          = 06446
  CsDiagnosticCode "PsErrIfInPat"                                  = 45696
  -- CsDiagnosticCode "PsErrLambdaCaseInPat"                          = Outdated 07636
  CsDiagnosticCode "PsErrCaseInPat"                                = 53786
  CsDiagnosticCode "PsErrLetInPat"                                 = 78892
  CsDiagnosticCode "PsErrLambdaInPat"                              = 00482
  CsDiagnosticCode "PsErrArrowExprInPat"                           = 04584
  -- CsDiagnosticCode "PsErrArrowCmdInPat"                            = 98980
  -- CsDiagnosticCode "PsErrArrowCmdInExpr"                           = 66043
  -- CsDiagnosticCode "PsErrViewPatInExpr"                            = 66228
  -- CsDiagnosticCode "PsErrLambdaCmdInFunAppCmd"                     = 12178
  -- CsDiagnosticCode "PsErrCaseCmdInFunAppCmd"                       = 92971
  -- CsDiagnosticCode "PsErrLambdaCaseCmdInFunAppCmd"                 = Outdated 47171
  -- CsDiagnosticCode "PsErrIfCmdInFunAppCmd"                         = 97005
  -- CsDiagnosticCode "PsErrLetCmdInFunAppCmd"                        = 70526
  -- CsDiagnosticCode "PsErrDoCmdInFunAppCmd"                         = 77808
  -- CsDiagnosticCode "PsErrDoInFunAppExpr"                           = 52095
  -- CsDiagnosticCode "PsErrMDoInFunAppExpr"                          = 67630
  CsDiagnosticCode "PsErrLambdaInFunAppExpr"                       = 06074
  CsDiagnosticCode "PsErrCaseInFunAppExpr"                         = 25037
  -- CsDiagnosticCode "PsErrLambdaCaseInFunAppExpr"                   = Outdated 77182
  CsDiagnosticCode "PsErrLetInFunAppExpr"                          = 90355
  CsDiagnosticCode "PsErrIfInFunAppExpr"                           = 01239
  -- CsDiagnosticCode "PsErrProcInFunAppExpr"                         = 04807
  -- CsDiagnosticCode "PsErrMalformedTyOrClDecl"                      = 47568
  -- CsDiagnosticCode "PsErrIllegalWhereInDataDecl"                   = 36952
  -- CsDiagnosticCode "PsErrIllegalDataTypeContext"                   = 87429
  -- CsDiagnosticCode "PsErrPrimStringInvalidChar"                    = 43080
  -- CsDiagnosticCode "PsErrSuffixAT"                                 = 33856
  CsDiagnosticCode "PsErrPrecedenceOutOfRange"                     = 25078
  CsDiagnosticCode "PsErrSemiColonsInCondExpr"                     = 75254
  -- CsDiagnosticCode "PsErrSemiColonsInCondCmd"                      = 18910
  CsDiagnosticCode "PsErrAtInPatPos"                               = 08382
  CsDiagnosticCode "PsErrParseErrorOnInput"                        = 66418
  CsDiagnosticCode "PsErrMalformedDecl"                            = 85316
  -- CsDiagnosticCode "PsErrNotADataCon"                              = 25742
  -- CsDiagnosticCode "PsErrInferredTypeVarNotAllowed"                = 57342
  -- CsDiagnosticCode "PsErrIllegalTraditionalRecordSyntax"           = 65719
  -- CsDiagnosticCode "PsErrParseErrorInCmd"                          = 03790
  CsDiagnosticCode "PsErrInPat"                                    = 07626
  -- CsDiagnosticCode "PsErrIllegalRoleName"                          = 09009
  CsDiagnosticCode "PsErrInvalidTypeSignature"                     = 94426
  CsDiagnosticCode "PsErrUnexpectedTypeInDecl"                     = 77878
  -- CsDiagnosticCode "PsErrInvalidPackageName"                       = 21926
  CsDiagnosticCode "PsErrParseRightOpSectionInPat"                 = 72516
  -- CsDiagnosticCode "PsErrIllegalGadtRecordMultiplicity"            = 37475
  -- CsDiagnosticCode "PsErrInvalidCApiImport"                        = 72744
  -- CsDiagnosticCode "PsErrMultipleConForNewtype"                    = 05380
  CsDiagnosticCode "PsErrUnicodeCharLooksLike"                     = 31623
  -- CsDiagnosticCode "PsErrInvalidPun"                               = 52943
  CsDiagnosticCode "PsErrInvalidKindRelation"                      = 17340
  CsDiagnosticCode "PsErrInTyPat"                                  = 47738
  CsDiagnosticCode "PsErrMalformedTyDecl"                          = 38833
  CsDiagnosticCode "PsErrUnexpectedAsPat"                          = 40732
  CsDiagnosticCode "PsErrTyLambdaInPat"                            = 10692
  CsDiagnosticCode "PsErrEmptyTyLamTy"                             = 30353
  CsDiagnosticCode "PsErrEmptyTyLam"                               = 11188

  -- Driver diagnostic codes
  CsDiagnosticCode "DriverMissingHomeModules"                      = 32850
  CsDiagnosticCode "DriverUnknownHiddenModules"                    = 38189
  CsDiagnosticCode "DriverUnknownReexportedModules"                = 68286
  CsDiagnosticCode "DriverUnusedPackages"                          = 42258
  CsDiagnosticCode "DriverUnnecessarySourceImports"                = 88907
  CsDiagnosticCode "DriverDuplicatedModuleDeclaration"             = 29235
  CsDiagnosticCode "DriverModuleNotFound"                          = 82272
  CsDiagnosticCode "DriverFileModuleNameMismatch"                  = 28623
  CsDiagnosticCode "DriverUnexpectedSignature"                     = 66004
  CsDiagnosticCode "DriverFileNotFound"                            = 49196
  CsDiagnosticCode "DriverStaticPointersNotSupported"              = 77799
  CsDiagnosticCode "DriverBackpackModuleNotFound"                  = 19971
  CsDiagnosticCode "DriverUserDefinedRuleIgnored"                  = 56147
  CsDiagnosticCode "DriverMixedSafetyImport"                       = 70172
  CsDiagnosticCode "DriverCannotLoadInterfaceFile"                 = 37141
  CsDiagnosticCode "DriverInferredSafeModule"                      = 58656
  CsDiagnosticCode "DriverMarkedTrustworthyButInferredSafe"        = 19244
  CsDiagnosticCode "DriverInferredSafeImport"                      = 82658
  CsDiagnosticCode "DriverCannotImportUnsafeModule"                = 44360
  CsDiagnosticCode "DriverMissingSafeHaskellMode"                  = 29747
  CsDiagnosticCode "DriverPackageNotTrusted"                       = 08674
  CsDiagnosticCode "DriverCannotImportFromUntrustedPackage"        = 75165
  CsDiagnosticCode "DriverRedirectedNoMain"                        = 95379
  CsDiagnosticCode "DriverHomePackagesNotClosed"                   = 03271
  CsDiagnosticCode "DriverInconsistentDynFlags"                    = 74335
  CsDiagnosticCode "DriverSafeHaskellIgnoredExtension"             = 98887
  CsDiagnosticCode "DriverPackageTrustIgnored"                     = 83552
  CsDiagnosticCode "DriverUnrecognisedFlag"                        = 93741
  CsDiagnosticCode "DriverDeprecatedFlag"                          = 53692

  -- To generate new random numbers:
  --  https://www.random.org/integers/?num=10&min=1&max=99999&col=1&base=10&format=plain
  --
  -- NB: never remove a return value from this type family!
  -- We need to ensure uniquess of diagnostic codes across Cs versions,
  -- and this includes outdated diagnostic codes for errors that Cs
  -- no longer reports. These are collected below.

type Outdated a = a

{- *********************************************************************
*                                                                      *
                 Recurring into an argument
*                                                                      *
********************************************************************* -}

type ConRecursInto :: Symbol -> Maybe Type
type family ConRecursInto con where
  ----------------------------------
  -- Constructors of CsMessage
  ConRecursInto "CsDriverMessage"         = 'Just DriverMessage
  ConRecursInto "CsPsMessage"             = 'Just PsMessage
  -- ConRecursInto "GhcTcRnMessage"           = 'Just TcRnMessage
  -- ConRecursInto "GhcDsMessage"             = 'Just DsMessage
  ConRecursInto "CsUnknownMessage"        = 'Just (UnknownDiagnostic CsMessageOpts)

  ----------------------------------
  -- Constructors of DriverMessage
  ConRecursInto "DriverUnknownMessage"     = 'Just (UnknownDiagnostic DriverMessageOpts)
  ConRecursInto "DriverPsHeaderMessage"    = 'Just PsMessage
  -- ConRecursInto "DriverInterfaceError"     = 'Just IfaceMessage

  -- ConRecursInto "CantFindErr"              = 'Just CantFindInstalled
  -- ConRecursInto "CantFindInstalledErr"     = 'Just CantFindInstalled

  -- ConRecursInto "CantFindInstalled"        = 'Just CantFindInstalledReason

  -- ConRecursInto "BadIfaceFile"                 = 'Just ReadInterfaceError
  -- ConRecursInto "FailedToLoadDynamicInterface" = 'Just ReadInterfaceError

  ----------------------------------
  -- Constructors of PsMessage
  ConRecursInto "PsUnknownMessage"         = 'Just (UnknownDiagnostic NoDiagnosticOpts)
  -- ConRecursInto "PsHeaderMessage"          = 'Just PsHeaderMessage

  ConRecursInto _                          = 'Nothing

{- *********************************************************************
*                                                                      *
                         Generics machinery
*                                                                      *
********************************************************************* -}

type GDiagnosticCode :: (Type -> Type) -> Constraint
class GDiagnosticCode f where
  gdiagnosticCode :: f a -> Maybe DiagnosticCode

type GDiagnosticCodes :: [Type] -> (Type -> Type) -> Constraint
class GDiagnosticCodes seen f where
  gdiagnosticCodes :: Map DiagnosticCode String

type ConstructorCode :: Symbol -> (Type -> Type)  -> Maybe Type -> Constraint
class ConstructorCode con f recur where
  gconstructorCode :: f a -> Maybe DiagnosticCode

type ConstructorCodes :: Symbol -> (Type -> Type) -> [Type] -> Maybe Type -> Constraint
class ConstructorCodes con f seen recur where
  gconstructorCodes :: Map DiagnosticCode String

instance (KnownConstructor con, KnownSymbol con) => ConstructorCode con f 'Nothing where
  gconstructorCode _ = Just $ DiagnosticCode "Cs" $ natVal' @(CsDiagnosticCode con) proxy#

instance (KnownConstructor con, KnownSymbol con) => ConstructorCodes con f seen 'Nothing where
  gconstructorCodes =
    Map.singleton
      (DiagnosticCode "Cs" $ natVal' @(CsDiagnosticCode con) proxy#)
      (symbolVal' @con proxy#)

instance {-# OVERLAPPING #-}
         ( ConRecursInto con ~ 'Just (UnknownDiagnostic opts)
         , HasType (UnknownDiagnostic opts) con f )
      => ConstructorCode con f ('Just (UnknownDiagnostic opts)) where
  gconstructorCode diag = case getType @(UnknownDiagnostic opts) @con @f diag of
    UnknownDiagnostic _ diag -> diagnosticCode diag

instance {-# OVERLAPPING #-}
         ( ConRecursInto con ~ 'Just (UnknownDiagnostic opts) )
      => ConstructorCodes con f seen ('Just (UnknownDiagnostic opts)) where
  gconstructorCodes = Map.empty

instance ( ConRecursInto con ~ 'Just ty, HasType ty con f
         , Generic ty, GDiagnosticCode (Rep ty) )
      => ConstructorCode con f ('Just ty) where
  gconstructorCode diag = gdiagnosticCode (from $ getType @ty @con @f diag)

instance ( ConRecursInto con ~ 'Just ty, HasType ty con f
         , Generic ty, GDiagnosticCodes (Insert ty seen) (Rep ty)
         , Seen seen ty )
      => ConstructorCodes con f seen ('Just ty) where
  gconstructorCodes =
    if wasSeen @seen @ty
    then Map.empty
    else gdiagnosticCodes @(Insert ty seen) @(Rep ty)

instance (ConstructorCode con f recur, recur ~ ConRecursInto con, KnownSymbol con)
      => GDiagnosticCode (M1 i ('MetaCons con x y) f) where
  gdiagnosticCode (M1 x) = gconstructorCode @con @f @recur x

instance (ConstructorCodes con f seen recur, recur ~ ConRecursInto con, KnownSymbol con)
      => GDiagnosticCodes seen (M1 i ('MetaCons con x y) f) where
  gdiagnosticCodes = gconstructorCodes @con @f @seen @recur

instance (GDiagnosticCode f, GDiagnosticCode g) => GDiagnosticCode (f :+: g) where
  gdiagnosticCode (L1 x) = gdiagnosticCode @f x
  gdiagnosticCode (R1 y) = gdiagnosticCode @g y

instance (GDiagnosticCodes seen f, GDiagnosticCodes seen g) => GDiagnosticCodes seen (f :+: g) where
  gdiagnosticCodes = Map.union (gdiagnosticCodes @seen @f) (gdiagnosticCodes @seen @g)

instance GDiagnosticCode f
      => GDiagnosticCode (M1 i ('MetaData nm mod pkg nt) f) where
  gdiagnosticCode (M1 x) = gdiagnosticCode @f x

instance GDiagnosticCodes seen f
      => GDiagnosticCodes seen (M1 i ('MetaData nm mod pkg nt) f) where
  gdiagnosticCodes = gdiagnosticCodes @seen @f

type family HasTypeQ (ty :: Type) f :: Maybe Type where
  HasTypeQ typ (M1 _ _ (K1 _ typ))
    = 'Just typ
  HasTypeQ typ (M1 _ _ x)
    = HasTypeQ typ x
  HasTypeQ typ (l :*: r)
    = Alt (HasTypeQ typ l) (HasTypeQ typ r)
  HasTypeQ typ (l :+: r)
    = Both (HasTypeQ typ l) (HasTypeQ typ r)
  HasTypeQ typ (K1 _ _)
    = 'Nothing
  HasTypeQ typ U1
    = 'Nothing
  HasTypeQ typ V1
    = 'Nothing

type family Both (m1 :: Maybe a) (m2 :: Maybe a) :: Maybe a where
  Both ('Just a) ('Just a) = 'Just a

type family Alt (m1 :: Maybe a) (m2 :: Maybe a) :: Maybe a where
  Alt ('Just a) _ = 'Just a
  Alt _ b = b

type HasType :: Type -> Symbol -> (Type -> Type) -> Constraint
class HasType ty orig f where
  getType :: f a -> ty

instance HasType ty orig (M1 i s (K1 x ty)) where
  getType (M1 (K1 x)) = x
instance HasTypeProd ty (HasTypeQ ty f) orig f g => HasType ty orig (f :*: g) where
  getType = getTypeProd @ty @(HasTypeQ ty f) @orig

class HasTypeProd ty lr orig f g where
  getTypeProd :: (f :*: g) a -> ty

instance HasType ty orig  f => HasTypeProd ty ('Just l) orig f g where
  getTypeProd (x :*: _) = getType @ty @orig @f x

instance HasType ty orig g => HasTypeProd ty 'Nothing orig f g where
  getTypeProd (_ :*: y) = getType @ty @orig @g y

type Seen :: [Type] -> Type -> Constraint
class Seen seen ty where
  wasSeen :: Bool

instance Seen '[] ty where
  wasSeen = False

instance {-# OVERLAPPING #-} Seen (ty ': tys) ty where
  wasSeen = True

instance Seen tys ty => Seen (ty' ': tys) ty where
  wasSeen = wasSeen @tys @ty

type Insert :: Type -> [Type] -> [Type]
type family Insert ty tys where
  Insert ty '[] = '[ty]
  Insert ty (ty ': tys) = ty ': tys
  Insert ty (ty' ': tys) = ty' ': Insert ty tys

{- *********************************************************************
*                                                                      *
               Custom type errors for diagnostic codes
*                                                                      *
********************************************************************* -}

instance {-# OVERLAPPABLE #-}
  TypeError
    (     'Text "The constructor '" ':<>: 'Text orig ':<>: 'Text "'"
    ':$$: 'Text "does not have any argument of type '" ':<>: 'ShowType ty ':<>: 'Text "'."
    ':$$: 'Text ""
    ':$$: 'Text "This is likely due to an incorrect type family equation:"
    ':$$: 'Text "  ConRecursInto \"" ':<>: 'Text orig ':<>: 'Text "\" = " ':<>: 'ShowType ty )
  => HasType ty orig f where
  getType = panic "getType: unreachable"

type KnownConstructor :: Symbol -> Constraint
type family KnownConstructor con where
  KnownConstructor con =
    KnownNatOrErr
      ( TypeError
        (     'Text "Missing diagnostic code for constructor "
        ':<>: 'Text "'" ':<>: 'Text con ':<>: 'Text "'."
        ':$$: 'Text ""
        ':$$: 'Text "See Cs.Types.Error.Codes"
        )
      )
      (CsDiagnosticCode con)

type KnownNatOrErr :: Constraint -> Nat -> Constraint
type KnownNatOrErr err n = (Assert err n, KnownNat n)

type Assert :: Constraint -> k -> Constraint
type family Assert err n where
  Assert _ Dummy = Dummy
  Assert _ n     = ()
data family Dummy :: k
