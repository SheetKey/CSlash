{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DeriveFunctor #-}

module CSlash.Pir
  ( module CSlash.Pir
  , module CSlash.Pir.Node
  , module CSlash.Pir.Expr
  ) where

import Prelude hiding ((<>))

import CSlash.Platform
import CSlash.Types.Var.Id
import GHC.Types.CostCentre
import CSlash.Pir.PLabel
import CSlash.Pir.BlockId
import CSlash.Pir.Node
-- import GHC.Runtime.Heap.Layout
import CSlash.Pir.Expr
import CSlash.Pir.Dataflow.Block
import CSlash.Pir.Dataflow.Graph
import CSlash.Pir.Dataflow.Label
import CSlash.Utils.Outputable

import Data.Void (Void)
import Data.List (intersperse)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS

-----------------------------------------------------------------------------
--  Pir, GenPir (Procedural intermediate representation)
-----------------------------------------------------------------------------

type PirProgram = [PirGroup]

type GenPirGroup d g = [GenPirDecl d g]

type DPirGroup = GenPirGroup PirStatics DPirGraph

type PirGroup = GenPirGroup PirStatics PirGraph

type RawPirGroup = GenPirGroup RawPirStatics PirGraph

-----------------------------------------------------------------------------
--  PirDecl, GenPirDecl
-----------------------------------------------------------------------------

data GenPirDecl d g
  = PirProc PLabel [PirFormal] g
  | PirData Section d
  deriving Functor

instance (OutputableP Platform d, OutputableP Platform g)
  => OutputableP Platform (GenPirDecl d g) where
  pdoc = pprTop

type DPirDecl = GenPirDecl PirStatics DPirGraph
type PirDecl = GenPirDecl PirStatics PirGraph
type PirDataDecl = GenPirDataDecl PirStatics
type GenPirDataDecl d = GenPirDecl d Void

pirDataDeclPirDecl :: GenPirDataDecl d -> GenPirDecl d g
pirDataDeclPirDecl = \case
    PirProc _ _ void -> case void of
    PirData section d -> PirData section d
{-# INLINE pirDataDeclPirDecl #-}

-----------------------------------------------------------------------------
--     Graphs
-----------------------------------------------------------------------------

type PirGraph = GenPirGraph PirNode
type DPirGraph = GenGenPirGraph DWrap PirNode

type GenPirGraph n = GenGenPirGraph LabelMap n

data GenGenPirGraph s n = PirGraph { g_entry :: BlockId, g_graph :: Graph' s Block n C C }

type PirBlock = Block PirNode C C

instance OutputableP Platform PirGraph where
  pdoc = pprPirGraph

toBlockMap :: PirGraph -> LabelMap PirBlock
toBlockMap PirGraph{ g_graph = GMany NothingO body NothingO } = body

pprPirGraph :: Platform -> PirGraph -> SDoc
pprPirGraph platform g
  = text "{" <> text "offset"
    $$ nest 2 (vcat $ map (pdoc platform) blocks)
    $$ text "}"
    where
      blocks = revPostorder g

revPostorder :: PirGraph -> [PirBlock]
revPostorder g = {-# SCC "revPostorder" #-} revPostorderFrom (toBlockMap g) (g_entry g)

toBlockList :: PirGraph -> [PirBlock]
toBlockList g = mapElems $ toBlockMap g

newtype DWrap a = DWrap [(BlockId, a)]

unDeterm :: DWrap a -> [(BlockId, a)]
unDeterm (DWrap f) = f

data ProfilingInfo
  = NoProfilingInfo
  deriving (Eq, Ord)

-----------------------------------------------------------------------------
--              Static Data
-----------------------------------------------------------------------------

data SectionType
  = Text
  | Data
  | ReadOnlyData
  deriving Show

data SectionProtection
  = ReadWriteSection
  | ReadOnlySection
  deriving Eq

sectionProtection :: Section -> SectionProtection
sectionProtection (Section t _) = case t of
  Text -> ReadOnlySection
  Data -> ReadWriteSection
  ReadOnlyData -> ReadOnlySection

data Section = Section SectionType PLabel

data PirStatic
  = PirStaticLit PirLit
  | PirString ByteString

instance OutputableP Platform PirStatic where
  pdoc = pprStatic

instance Outputable PirStatic where
  ppr (PirStaticLit lit) = text "PirStaticLit" <+> ppr lit
  ppr (PirString _) = text "PirString"

data GenPirStatics (rawOnly :: Bool) where
  PirStatics
    :: PLabel
    -> [PirLit]
    -> GenPirStatics 'False

  PirStaticsRaw
    :: PLabel
    -> [PirStatic]
    -> GenPirStatics a

instance OutputableP Platform (GenPirStatics a) where
  pdoc = pprStatics

type PirStatics = GenPirStatics 'False
type RawPirStatics = GenPirStatics 'True

-------------------------------------------------------------------------------
-- Basic blocks consisting of lists
-------------------------------------------------------------------------------

data GenBasicBlock i = BasicBlock BlockId [i]
  deriving Functor

blockId :: GenBasicBlock i -> BlockId
blockId (BasicBlock blk_id _) = blk_id

newtype ListGraph i = ListGraph [GenBasicBlock i]
  deriving Functor

instance Outputable instr => Outputable (ListGraph instr) where
  ppr (ListGraph blocks) = vcat (map ppr blocks)

instance OutputableP env instr => OutputableP env (ListGraph instr) where
  pdoc env g = ppr (fmap (pdoc env) g)

instance Outputable instr => Outputable (GenBasicBlock instr) where
  ppr = pprBBlock

instance OutputableP env instr => OutputableP env (GenBasicBlock instr) where
  pdoc env block = ppr (fmap (pdoc env) block)

pprBBlock :: Outputable stmt => GenBasicBlock stmt -> SDoc
pprBBlock (BasicBlock ident stmts) =
  hang (ppr ident <> colon) 4 (vcat (map ppr stmts))

----------------------------------------------------------------------------
-- Pretty-printing Pir
----------------------------------------------------------------------------
  
pprPirGroup
  :: (OutputableP Platform d, OutputableP Platform g)
  => Platform -> GenPirGroup d g -> SDoc
pprPirGroup platform tops
  = vcat $ intersperse blankLine $ map (pprTop platform) tops

pprTop
  :: (OutputableP Platform d, OutputableP Platform i)
  => Platform -> GenPirDecl d i -> SDoc
pprTop platform (PirProc lbl formals graph)
  = vcat [ pdoc platform lbl <> lparen <> pprFormals formals <> rparen <+> lbrace
         , nest 4 $ pdoc platform graph
         , rbrace ]
pprTop platform (PirData section ds)
  = (hang (pprSection platform section <+> lbrace) 4 (pdoc platform ds)) $$ rbrace

pprFormals :: PirFormals -> SDoc
pprFormals fs = interppSP fs -- TODO: check this is correct

----------------------------------------------------------------------------
-- Static data.
----------------------------------------------------------------------------

pprStatics :: Platform -> GenPirStatics a -> SDoc
pprStatics platform (PirStatics lbl payload)
  = pdoc platform lbl <> colon <+> pdoc platform payload
pprStatics platform (PirStaticsRaw lbl ds)
  = vcat ((pdoc platform lbl <> colon)
          : map (pprStatic platform) ds)

pprStatic :: Platform -> PirStatic -> SDoc
pprStatic platform s = case s of
  PirStaticLit lit -> nest 4 $ text "const" <+> pdoc platform lit <> semi
  PirString s' -> nest 4 $ text "i8[]" <+> text (show s')

----------------------------------------------------------------------------
-- Data sections
----------------------------------------------------------------------------

pprSection :: Platform -> Section -> SDoc
pprSection platform (Section t suffix)
  = text "section" <+> doubleQuotes (pprSectionType t <+> char '.' <+> pdoc platform suffix)

pprSectionType :: SectionType -> SDoc
pprSectionType s = doubleQuotes $ case s of
  Text -> text "text"
  Data -> text "data"
  ReadOnlyData -> text "readonly"
