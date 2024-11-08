{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}

module CSlash.Rename.Pat where

-- import {-# SOURCE #-} GHC.Rename.Expr ( rnLExpr )
-- import {-# SOURCE #-} GHC.Rename.Splice ( rnSplicePat, rnSpliceTyPat )

import CSlash.Cs
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad
-- import GHC.Tc.Utils.TcMType ( hsOverLitName )
import CSlash.Rename.Env
import CSlash.Rename.Fixity
import CSlash.Rename.Utils
  ( newLocalBndrRn, bindLocalNames, warnUnusedMatches, newLocalBndrRn
  {-, checkDupNames, checkDupAndShadowedNames
  , wrapGenSpan, genHsApps, genLHsVar, genHsIntegralLit, delLocalNames, typeAppErr-} )
-- import GHC.Rename.HsType
import CSlash.Builtin.Names

import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.Name.Reader
import CSlash.Types.Unique.Set

import CSlash.Types.Basic
import CSlash.Types.SourceText
import CSlash.Utils.Misc
import CSlash.Data.FastString ( uniqCompareFS )
import CSlash.Data.List.SetOps( removeDups )
import CSlash.Data.Bag ( Bag, unitBag, unionBags, emptyBag, listToBag, bagToList )
import CSlash.Utils.Outputable
import CSlash.Utils.Panic.Plain
import CSlash.Types.SrcLoc
-- import CSlash.Types.Literal   ( inCharRange )
import CSlash.Types.GREInfo   ( ConInfo(..){-, conInfoFields-} )
-- import CSlash.Builtin.Types   ( nilDataCon )
import CSlash.Core.DataCon
-- import CSlash.Core.TyCon      ( isKindName )

import Control.Monad       ( when, ap, guard, unless )
import Data.Foldable
import Data.Function       ( on )
import Data.Functor.Identity ( Identity (..) )
import qualified Data.List.NonEmpty as NE
import Data.Maybe
import Data.Ratio
import qualified Data.Semigroup as S
import Control.Monad.Trans.Writer.CPS
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Data.Functor ((<&>))
-- import GHC.Rename.Doc (rnLHsDoc)
import CSlash.Types.Hint
import CSlash.Types.Fixity (LexicalFixity(..))
import Data.Coerce

{- *****************************************************
*                                                      *
        The CpsRn Monad
*                                                      *
***************************************************** -}

newtype CpsRn b = CpsRn { unCpsRn :: forall r. (b -> RnM (r, FreeVars)) -> RnM (r, FreeVars) }
  deriving (Functor)

instance Applicative CpsRn where
  pure x = CpsRn (\k -> k x)
  (<*>) = ap

instance Monad CpsRn where
  (CpsRn m) >>= mk = CpsRn (\k -> m (\v -> unCpsRn (mk v) k))

runCps :: CpsRn a -> RnM (a, FreeVars)
runCps (CpsRn m) = m (\r -> return (r, emptyFVs))

liftCps :: RnM a -> CpsRn a
liftCps rn_thing = CpsRn (\k -> rn_thing >>= k)

liftCpsFV :: RnM (a, FreeVars) -> CpsRn a
liftCpsFV rn_thing = CpsRn (\k -> do (v, fvs1) <- rn_thing
                                     (r, fvs2) <- k v
                                     return (r, fvs1 `plusFV` fvs2))

{- *****************************************************
*                                                      *
        Name makers
*                                                      *
***************************************************** -}

data NameMaker
  = LamMk Bool
  | LetMk TopLevelFlag MiniFixityEnv

topRecNameMaker :: MiniFixityEnv -> NameMaker
topRecNameMaker fix_env = LetMk TopLevel fix_env

newPatLName :: NameMaker -> LocatedN RdrName -> CpsRn (LocatedN Name)
newPatLName name_maker rdr_name@(L loc _) = (L loc) <$>  newPatName name_maker rdr_name

newPatName :: NameMaker -> LocatedN RdrName -> CpsRn Name
newPatName (LamMk report_unused) rdr_name = CpsRn $ \ thing_inside -> do
  name <- newLocalBndrRn rdr_name
  (res, fvs) <- bindLocalNames [name] (thing_inside name)
  when report_unused $ warnUnusedMatches [name] fvs
  return (res, name `delFV` fvs)
newPatName (LetMk is_top fix_env) rdr_name = CpsRn $ \ thing_inside -> do
  name <- case is_top of
            NotTopLevel -> newLocalBndrRn rdr_name
            TopLevel -> newTopSrcBinder rdr_name
  bindLocalNames [name]
    $ addLocalFixities fix_env [name]
    $ thing_inside name

{- *****************************************************
*                                                      *
        External entry points
*                                                      *
***************************************************** -}

applyNameMaker :: NameMaker -> LocatedN RdrName -> RnM (LocatedN Name)
applyNameMaker mk rdr = fst <$> runCps (newPatLName mk rdr)
