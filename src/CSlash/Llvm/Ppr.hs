{-# LANGUAGE TypeApplications #-}

module CSlash.Llvm.Ppr where

import Prelude hiding ((<>))

import CSlash.Llvm.Syntax
import CSlash.Llvm.MetaData
import CSlash.Llvm.Types

import Data.List ( intersperse )
import CSlash.Utils.Outputable

import CSlash.Llvm.Config
import CSlash.Utils.Panic
import CSlash.Types.Unique

--------------------------------------------------------------------------------
-- * Top Level Print functions
--------------------------------------------------------------------------------

ppLlvmModule :: IsDoc doc => LlvmCgConfig -> LlvmModule -> doc
ppLlvmModule opts (LlvmModule comments aliases meta globals decls funcs)
  = ppLlvmComments comments $$ newLine $$
    ppLlvmAliases aliases $$ newLine $$
    ppLlvmMetas opts meta $$ newLine $$
    ppLlvmGlobals opts globals $$ newLine $$
    ppLlvmFunctionDecls decls $$ newLine $$
    ppLlvmFunctions opts funcs   
{-# SPECIALIZE ppLlvmModule :: LlvmCgConfig -> LlvmModule -> SDoc #-}
{-# SPECIALIZE ppLlvmModule :: LlvmCgConfig -> LlvmModule -> HDoc #-}

ppLlvmComments :: IsDoc doc => [LMString] -> doc
ppLlvmComments comments = lines_ $ map ppLlvmComment comments
{-# SPECIALIZE ppLlvmComments :: [LMString] -> SDoc #-}
{-# SPECIALIZE ppLlvmComments :: [LMString] -> HDoc #-}

ppLlvmComment :: IsLine doc => LMString -> doc
ppLlvmComment com = semi <+> ftext com
{-# SPECIALIZE ppLlvmComment :: LMString -> SDoc #-}
{-# SPECIALIZE ppLlvmComment :: LMString -> HLine #-}

ppLlvmGlobals :: IsDoc doc => LlvmCgConfig -> [LMGlobal] -> doc
ppLlvmGlobals opts ls = lines_ $ map (ppLlvmGlobal opts) ls
{-# SPECIALIZE ppLlvmGlobals :: LlvmCgConfig -> [LMGlobal] -> SDoc #-}
{-# SPECIALIZE ppLlvmGlobals :: LlvmCgConfig -> [LMGlobal] -> HDoc #-}

ppLlvmGlobal :: IsLine doc => LlvmCgConfig -> LMGlobal -> doc
ppLlvmGlobal opts (LMGlobal var@(LMGlobalVar _ _ link x a c) dat) =
  let sect = case x of
               Just x' -> text ", section" <+> doubleQuotes (ftext x')
               Nothing -> empty

      align = case a of
                Just a' -> text ", align" <+> int a'
                Nothing -> empty

      rhs = case dat of
              Just stat -> pprSpecialStatic opts stat
              Nothing -> ppLlvmType (pLower $ getVarType var)

      const = case c of
                Global -> "global"
                Constant -> "constant"
                Alias -> "alias"

  in ppAssignment opts var
     $ ppLlvmLinkageType link
     <+> text const
     <+> rhs
     <> sect
     <> align

ppLlvmGlobal opts (LMGlobal var val) = pprPanic "ppLlvmGlobal" $
  text "Non Global var ppr as global!"
  <> ppVar opts var
  <> text "="
  <> ppr (fmap (ppStatic @SDoc opts) val)
{-# SPECIALIZE ppLlvmGlobal :: LlvmCgConfig -> LMGlobal -> SDoc #-}
{-# SPECIALIZE ppLlvmGlobal :: LlvmCgConfig -> LMGlobal -> HLine #-}

ppLlvmAliases :: IsDoc doc => [LlvmAlias] -> doc
ppLlvmAliases tys = lines_ $ map ppLlvmAlias tys
{-# SPECIALIZE ppLlvmAliases :: [LlvmAlias] -> SDoc #-}
{-# SPECIALIZE ppLlvmAliases :: [LlvmAlias] -> HDoc #-}

ppLlvmAlias :: IsLine doc => LlvmAlias -> doc
ppLlvmAlias (name, ty)
  = char '%' <> ftext name <+> equals <+> text "type" <+> ppLlvmType ty
{-# SPECIALIZE ppLlvmAlias :: LlvmAlias -> SDoc #-}
{-# SPECIALIZE ppLlvmAlias :: LlvmAlias -> HLine #-}

ppLlvmMetas :: IsDoc doc => LlvmCgConfig -> [MetaDecl] -> doc
ppLlvmMetas opts metas = lines_ $ map (ppLlvmMeta opts) metas
{-# SPECIALIZE ppLlvmMetas :: LlvmCgConfig -> [MetaDecl] -> SDoc #-}
{-# SPECIALIZE ppLlvmMetas :: LlvmCgConfig -> [MetaDecl] -> HDoc #-}

ppLlvmMeta :: IsLine doc => LlvmCgConfig -> MetaDecl -> doc
ppLlvmMeta opts (MetaUnnamed n m)
  = ppMetaId n <+> equals <+> ppMetaExpr opts m
ppLlvmMeta _ (MetaNamed n m)
  = exclamation <> ftext n <+> equals <+> exclamation <> braces nodes
  where nodes = hcat $ intersperse comma $ map ppMetaId m
{-# SPECIALIZE ppLlvmMeta :: LlvmCgConfig -> MetaDecl -> SDoc #-}
{-# SPECIALIZE ppLlvmMeta :: LlvmCgConfig -> MetaDecl -> HLine #-}

ppLlvmFunctions :: IsDoc doc => LlvmCgConfig -> LlvmFunctions -> doc
ppLlvmFunctions opts funcs = vcat $ map (ppLlvmFunction opts) funcs
{-# SPECIALIZE ppLlvmFunctions :: LlvmCgConfig -> LlvmFunctions -> SDoc #-}
{-# SPECIALIZE ppLlvmFunctions :: LlvmCgConfig -> LlvmFunctions -> HDoc #-}

ppLlvmFunction :: IsDoc doc => LlvmCgConfig -> LlvmFunction -> doc
ppLlvmFunction opts fun =
  let attrDoc = ppSpaceJoin ppLlvmFuncAttr (funcAttrs fun)
      secDoc = case funcSect fun of
                 Just s' -> text "section" <+> (doubleQuotes $ ftext s')
                 Nothing -> empty
      prefixDoc = case funcPrefix fun of
                    Just v -> text "prefix" <+> ppStatic opts v
                    Nothing -> empty
  in vcat
     [ line $ text "define" <+> ppLlvmFunctionHeader (funcDecl fun) (funcArgs fun)
       <+> attrDoc <+> secDoc <+> prefixDoc
     , line lbrace
     , ppLlvmBlocks opts (funcBody fun)
     , line rbrace
     , newLine
     , newLine ]
{-# SPECIALIZE ppLlvmFunction :: LlvmCgConfig -> LlvmFunction -> SDoc #-}
{-# SPECIALIZE ppLlvmFunction :: LlvmCgConfig -> LlvmFunction -> HDoc #-}

ppLlvmFunctionHeader :: IsLine doc => LlvmFunctionDecl -> [LMString] -> doc
ppLlvmFunctionHeader (LlvmFunctionDecl n l c r p a) args =
  let align = case a of
                Just a' -> text " align " <> int a'
                Nothing -> empty
      args' = zipWith (\(ty, p) n -> ppLlvmType ty <+> ppSpaceJoin ppLlvmParamAttr p
                        <+> char '%' <> ftext n)
              p args
  in ppLlvmLinkageType l
     <+> ppLlvmCallConvention c
     <+> ppLlvmType r
     <+> char '@' <> ftext n
     <> lparen <> hsep (punctuate comma args') <> rparen
     <> align
{-# SPECIALIZE ppLlvmFunctionHeader :: LlvmFunctionDecl -> [LMString] -> SDoc #-}
{-# SPECIALIZE ppLlvmFunctionHeader :: LlvmFunctionDecl -> [LMString] -> HLine #-}

ppLlvmFunctionDecls :: IsDoc doc => LlvmFunctionDecls -> doc
ppLlvmFunctionDecls decs = vcat $ map ppLlvmFunctionDecl decs
{-# SPECIALIZE ppLlvmFunctionDecls :: LlvmFunctionDecls -> SDoc #-}
{-# SPECIALIZE ppLlvmFunctionDecls :: LlvmFunctionDecls -> HDoc #-}

ppLlvmFunctionDecl :: IsDoc doc => LlvmFunctionDecl -> doc
ppLlvmFunctionDecl (LlvmFunctionDecl n l c r p a) =
  let align = case a of
                Just a' -> text " align" <+> int a'
                Nothing -> empty
      args = hcat $ intersperse (comma <> space) $
             map (\(t, a) -> ppLlvmType t <+> ppSpaceJoin ppLlvmParamAttr a) p
  in lines_
     [ text "declare" <+> ppLlvmLinkageType l <+> ppLlvmCallConvention c
       <+> ppLlvmType r <+> char '@' <> ftext n <> lparen <> args <> rparen <> align
     , empty ]
{-# SPECIALIZE ppLlvmFunctionDecl :: LlvmFunctionDecl -> SDoc #-}
{-# SPECIALIZE ppLlvmFunctionDecl :: LlvmFunctionDecl -> HDoc #-}

ppLlvmBlocks :: IsDoc doc => LlvmCgConfig -> LlvmBlocks -> doc
ppLlvmBlocks opts blocks = vcat $ map (ppLlvmBlock opts) blocks
{-# SPECIALIZE ppLlvmBlocks :: LlvmCgConfig -> LlvmBlocks -> SDoc #-}
{-# SPECIALIZE ppLlvmBlocks :: LlvmCgConfig -> LlvmBlocks -> HDoc #-}

ppLlvmBlock :: IsDoc doc => LlvmCgConfig -> LlvmBlock -> doc
ppLlvmBlock opts (LlvmBlock blockId stmts) =
  let isLabel (MkLabel _) = True
      isLabel _ = False
      (block, rest) = break isLabel stmts
      ppRest = case rest of
                 MkLabel id : xs -> ppLlvmBlock opts (LlvmBlock id xs)
                 _ -> empty
  in vcat $
     line (ppLlvmBlockLabel blockId)
     : map (ppLlvmStatement opts) block
     ++ [empty, ppRest]
{-# SPECIALIZE ppLlvmBlock :: LlvmCgConfig -> LlvmBlock -> SDoc #-}
{-# SPECIALIZE ppLlvmBlock :: LlvmCgConfig -> LlvmBlock -> HDoc #-}

ppLlvmBlockLabel :: IsLine doc => LlvmBlockId -> doc
ppLlvmBlockLabel id = pprUniqueAlways id <> colon
{-# SPECIALIZE ppLlvmBlockLabel :: LlvmBlockId -> SDoc #-}
{-# SPECIALIZE ppLlvmBlockLabel :: LlvmBlockId -> HLine #-}

ppLlvmStatement :: IsDoc doc => LlvmCgConfig -> LlvmStatement -> doc
ppLlvmStatement opts stmt =
  let ind = line . (text "  " <>)
  in case stmt of
       Assignment dst expr -> ind $ ppAssignment opts dst (ppLlvmExpression opts expr)
       Fence st ord -> ind $ ppFence st ord
       Branch target -> ind $ ppBranch opts target
       BranchIf cond ifT ifF -> ind $ ppBranchIf opts cond ifT ifF
       Comment comments -> ppLlvmComments comments
       MkLabel label -> line $ ppLlvmBlockLabel label
       Store value ptr align metas -> ind $ ppStore opts value ptr align metas
       Switch scrut def tgs -> ppSwitch opts scrut def tgs
       Return result -> ind $ ppReturn opts result
       Expr expr -> ind $ ppLlvmExpression opts expr
       Unreachable -> ind $ text "unreachable"
       Nop -> line empty
{-# SPECIALIZE ppLlvmStatement :: LlvmCgConfig -> LlvmStatement -> SDoc #-}
{-# SPECIALIZE ppLlvmStatement :: LlvmCgConfig -> LlvmStatement -> HDoc #-}

ppLlvmExpression :: IsLine doc => LlvmCgConfig -> LlvmExpression -> doc
ppLlvmExpression opts expr
  = case expr of
      Alloca tp amount -> ppAlloca opts tp amount
      LlvmOp op left right -> ppMachOp opts op left right
      Call tp fp args attrs -> ppCall opts tp fp (map MetaVar args) attrs
      CallM tp fp args attrs -> ppCall opts tp fp args attrs
      Cast op from to -> ppCast opts op from to
      Compare op left right -> ppCmpOp opts op left right
      ExtractV struct idx -> ppExtractV opts struct idx
      Insert vec elt idx -> ppInsert opts vec elt idx
      -- Shuffle v1 v2 idxs -> ppShuffle opts v1 v2 idxs
      GetElemPtr inb ptr indexes -> ppGetElementPtr opts inb ptr indexes
      Load ptr align -> ppLoad opts ptr align
      ALoad ord st ptr -> ppALoad opts ord st ptr
      AtomicRMW aop tgt src ordering -> ppAtomicRMW opts aop tgt src ordering
      CmpXChg addr old new s_ord f_ord -> ppCmpXChg opts addr old new s_ord f_ord
      Phi tp predecessors -> ppPhi opts tp predecessors
      Asm asm c ty v se sk -> ppAsm opts asm c ty v se sk
      MExpr meta expr -> ppMetaAnnotExpr opts meta expr
{-# SPECIALIZE ppLlvmExpression :: LlvmCgConfig -> LlvmExpression -> SDoc #-}
{-# SPECIALIZE ppLlvmExpression :: LlvmCgConfig -> LlvmExpression -> HLine #-}

ppMetaExpr :: IsLine doc => LlvmCgConfig -> MetaExpr -> doc
ppMetaExpr opts e = case e of
  MetaVar (LMLitVar (LMNullLit _)) -> text "null"
  MetaStr s -> char '!' <> doubleQuotes (ftext s)
  MetaLit l -> ppTypeLit opts l
  MetaNode n -> ppMetaId n
  MetaVar v -> ppVar opts v
  MetaStruct es -> char '!' <> braces (ppCommaJoin (ppMetaExpr opts) es)
{-# SPECIALIZE ppMetaExpr :: LlvmCgConfig -> MetaExpr -> SDoc #-}
{-# SPECIALIZE ppMetaExpr :: LlvmCgConfig -> MetaExpr -> HLine #-}

--------------------------------------------------------------------------------
-- * Individual print functions
--------------------------------------------------------------------------------

ppCall
  :: IsLine doc
  => LlvmCgConfig
  -> LlvmCallType
  -> LlvmVar
  -> [MetaExpr]
  -> [LlvmFuncAttr]
  -> doc
ppCall opts ct fptr args attrs = case fptr of
  LMLocalVar _ (LMPointer (LMFunction d)) -> ppCall' d

  LMGlobalVar _ (LMFunction d) _ _ _ _ -> ppCall' d

  _ -> error $
       "ppCall called with non LMFunction type!\nMust be "
       ++ " called with either global var of function type or "
       ++ "local var of pointer function type."

  where
    ppCall' (LlvmFunctionDecl _ _ cc ret params _) =
      let tc = if ct == TailCall then text "tail " else empty
          ppValues = ppCallParams opts (map snd params) args
          ppArgTy = ppCommaJoin (ppLlvmType . fst) params
          fnty = space <> lparen <> ppArgTy <> rparen
          attrDoc = ppSpaceJoin ppLlvmFuncAttr attrs
      in tc <> text "call" <+> ppLlvmCallConvention cc <+> ppLlvmType ret
         <> fnty <+> ppName opts fptr <> lparen <+> ppValues <+> rparen <+> attrDoc

    ppCallParams opts attrs args =
      hsep $ punctuate comma $ zipWith ppCallMetaExpr attrs args
      where
        ppCallMetaExpr attrs (MetaVar v) = ppVar' attrs opts v
        ppCallMetaExpr _ v = text "metadata" <+> ppMetaExpr opts v
{-# SPECIALIZE ppCall :: LlvmCgConfig -> LlvmCallType -> LlvmVar -> [MetaExpr] -> [LlvmFuncAttr] -> SDoc #-}
{-# SPECIALIZE ppCall :: LlvmCgConfig -> LlvmCallType -> LlvmVar -> [MetaExpr] -> [LlvmFuncAttr] -> HLine #-}

ppMachOp :: IsLine doc => LlvmCgConfig -> LlvmMachOp -> LlvmVar -> LlvmVar -> doc
ppMachOp opts op left right =
  ppLlvmMachOp op <+> ppLlvmType (getVarType left) <+> ppName opts left
  <> comma <+> ppName opts right
{-# SPECIALIZE ppMachOp :: LlvmCgConfig -> LlvmMachOp -> LlvmVar -> LlvmVar -> SDoc #-}
{-# SPECIALIZE ppMachOp :: LlvmCgConfig -> LlvmMachOp -> LlvmVar -> LlvmVar -> HLine #-}

ppCmpOp :: IsLine doc => LlvmCgConfig -> LlvmCmpOp -> LlvmVar -> LlvmVar -> doc 
ppCmpOp opts op left right =
  let cmpOp
        | isInt (getVarType left) && isInt (getVarType right)
        = text "icmp"
        | isFloat (getVarType left) && isFloat (getVarType right)
        = text "fcmp"
        | otherwise = panic "trying to compare different llvm types"
  in cmpOp <+> ppLlvmCmpOp op <+> ppLlvmType (getVarType left)
     <+> ppName opts left <> comma <+> ppName opts right
{-# SPECIALIZE ppCmpOp :: LlvmCgConfig -> LlvmCmpOp -> LlvmVar -> LlvmVar -> SDoc #-}
{-# SPECIALIZE ppCmpOp :: LlvmCgConfig -> LlvmCmpOp -> LlvmVar -> LlvmVar -> HLine #-}

ppAssignment :: IsLine doc => LlvmCgConfig -> LlvmVar -> doc -> doc
ppAssignment opts var expr = ppName opts var <+> equals <+> expr
{-# SPECIALIZE ppAssignment :: LlvmCgConfig -> LlvmVar -> SDoc -> SDoc #-}
{-# SPECIALIZE ppAssignment :: LlvmCgConfig -> LlvmVar -> HLine -> HLine #-}

ppFence :: IsLine doc => Bool -> LlvmSyncOrdering -> doc
ppFence st ord =
  let singleThread = if st then text "singlethread" else empty
  in text "fence" <+> singleThread <+> ppSyncOrdering ord
{-# SPECIALIZE ppFence :: Bool -> LlvmSyncOrdering -> SDoc #-}
{-# SPECIALIZE ppFence :: Bool -> LlvmSyncOrdering -> HLine #-}

ppSyncOrdering :: IsLine doc => LlvmSyncOrdering -> doc
ppSyncOrdering SyncUnord = text "unordered"
ppSyncOrdering SyncMonotonic = text "monotonic"
ppSyncOrdering SyncAcquire = text "acquire"
ppSyncOrdering SyncRelease = text "release"
ppSyncOrdering SyncAcqRel = text "acq_rel"
ppSyncOrdering SyncSeqCst = text "seq_cst"
{-# SPECIALIZE ppSyncOrdering :: LlvmSyncOrdering -> SDoc #-}
{-# SPECIALIZE ppSyncOrdering :: LlvmSyncOrdering -> HLine #-}

ppAtomicOp :: IsLine doc => LlvmAtomicOp -> doc
ppAtomicOp LAO_Xchg = text "xchg"
ppAtomicOp LAO_Add = text "add"
ppAtomicOp LAO_Sub = text "sub"
ppAtomicOp LAO_And = text "and"
ppAtomicOp LAO_Nand = text "nand"
ppAtomicOp LAO_Or = text "or"
ppAtomicOp LAO_Xor = text "xor"
ppAtomicOp LAO_Max = text "max"
ppAtomicOp LAO_Min = text "min"
ppAtomicOp LAO_Umax = text "umax"
ppAtomicOp LAO_Umin = text "umin"
{-# SPECIALIZE ppAtomicOp :: LlvmAtomicOp -> SDoc #-}
{-# SPECIALIZE ppAtomicOp :: LlvmAtomicOp -> HLine #-}

ppAtomicRMW
  :: IsLine doc
  => LlvmCgConfig -> LlvmAtomicOp -> LlvmVar -> LlvmVar -> LlvmSyncOrdering -> doc
ppAtomicRMW opts aop tgt src ordering =
  text "atomicrmw" <+> ppAtomicOp aop <+> ppVar opts tgt <> comma
  <+> ppVar opts src <+> ppSyncOrdering ordering
{-# SPECIALIZE ppAtomicRMW :: LlvmCgConfig -> LlvmAtomicOp -> LlvmVar -> LlvmVar -> LlvmSyncOrdering -> SDoc #-}
{-# SPECIALIZE ppAtomicRMW :: LlvmCgConfig -> LlvmAtomicOp -> LlvmVar -> LlvmVar -> LlvmSyncOrdering -> HLine #-}

ppCmpXChg
  :: IsLine doc
  => LlvmCgConfig -> LlvmVar -> LlvmVar -> LlvmVar -> LlvmSyncOrdering -> LlvmSyncOrdering -> doc
ppCmpXChg opts addr old new s_ord f_ord =
  text "cmpxchg" <+> ppVar opts addr <> comma <+> ppVar opts old <> comma <+> ppVar opts new
  <+> ppSyncOrdering s_ord <+> ppSyncOrdering f_ord
{-# SPECIALIZE ppCmpXChg :: LlvmCgConfig -> LlvmVar -> LlvmVar -> LlvmVar -> LlvmSyncOrdering -> LlvmSyncOrdering -> SDoc #-}
{-# SPECIALIZE ppCmpXChg :: LlvmCgConfig -> LlvmVar -> LlvmVar -> LlvmVar -> LlvmSyncOrdering -> LlvmSyncOrdering -> HLine #-}

ppLoad :: IsLine doc => LlvmCgConfig -> LlvmVar -> LMAlign -> doc
ppLoad opts var alignment =
  text "load" <+> ppLlvmType derefType <> comma <+> ppVar opts var <> align
  where
    derefType = pLower $ getVarType var
    align = case alignment of
              Just n -> text ", align" <+> int n
              Nothing -> empty
{-# SPECIALIZE ppLoad :: LlvmCgConfig -> LlvmVar -> LMAlign -> SDoc #-}
{-# SPECIALIZE ppLoad :: LlvmCgConfig -> LlvmVar -> LMAlign -> HLine #-}

ppALoad :: IsLine doc => LlvmCgConfig -> LlvmSyncOrdering -> SingleThreaded -> LlvmVar -> doc
ppALoad opts ord st var =
  let alignment = llvmWidthInBits (llvmCgPlatform opts) (getVarType var) `quot` 8
      align = text ", align" <+> int alignment
      sThreaded = if st then text " singlethread" else empty
      derefType = pLower $ getVarType var
  in text "load atomic" <+> ppLlvmType derefType <> comma <+> ppVar opts var <> sThreaded
     <+> ppSyncOrdering ord <> align
{-# SPECIALIZE ppALoad :: LlvmCgConfig -> LlvmSyncOrdering -> SingleThreaded -> LlvmVar -> SDoc #-}
{-# SPECIALIZE ppALoad :: LlvmCgConfig -> LlvmSyncOrdering -> SingleThreaded -> LlvmVar -> HLine #-}

ppStore :: IsLine doc => LlvmCgConfig -> LlvmVar -> LlvmVar -> LMAlign -> [MetaAnnot] -> doc
ppStore opts val dst alignment metas =
  text "store" <+> ppVar opts val <> comma <+> ppVar opts dst <> align
  <+> ppMetaAnnots opts metas
  where align = case alignment of
                  Just n -> text ", align" <+> int n
                  Nothing -> empty
{-# SPECIALIZE ppStore :: LlvmCgConfig -> LlvmVar -> LlvmVar -> LMAlign -> [MetaAnnot] -> SDoc #-}
{-# SPECIALIZE ppStore :: LlvmCgConfig -> LlvmVar -> LlvmVar -> LMAlign -> [MetaAnnot] -> HLine #-}

ppCast :: IsLine doc => LlvmCgConfig -> LlvmCastOp -> LlvmVar -> LlvmType -> doc
ppCast opts op from to =
  ppLlvmCastOp op
  <+> ppLlvmType (getVarType from) <+> ppName opts from
  <+> text "to"
  <+> ppLlvmType to
{-# SPECIALIZE ppCast :: LlvmCgConfig -> LlvmCastOp -> LlvmVar -> LlvmType -> SDoc #-}
{-# SPECIALIZE ppCast :: LlvmCgConfig -> LlvmCastOp -> LlvmVar -> LlvmType -> HLine #-}

ppAlloca :: IsLine doc => LlvmCgConfig -> LlvmType -> Int -> doc
ppAlloca opts tp amount =
  let amount' = LMLitVar $ LMIntLit (toInteger amount) i32
  in text "alloca" <+> ppLlvmType tp <> comma <+> ppVar opts amount'
{-# SPECIALIZE ppAlloca :: LlvmCgConfig -> LlvmType -> Int -> SDoc #-}
{-# SPECIALIZE ppAlloca :: LlvmCgConfig -> LlvmType -> Int -> HLine #-}

ppGetElementPtr :: IsLine doc => LlvmCgConfig -> Bool -> LlvmVar -> [LlvmVar] -> doc
ppGetElementPtr opts inb ptr idx =
  let indexes = comma <+> ppCommaJoin (ppVar opts) idx
      inbound = if inb then text "inbounds" else empty
      derefType = pLower $ getVarType ptr
  in text "getelementptr" <+> inbound <+> ppLlvmType derefType <> comma
     <+> ppVar opts ptr <> indexes
{-# SPECIALIZE ppGetElementPtr :: LlvmCgConfig -> Bool -> LlvmVar -> [LlvmVar] -> SDoc #-}
{-# SPECIALIZE ppGetElementPtr :: LlvmCgConfig -> Bool -> LlvmVar -> [LlvmVar] -> HLine #-}

ppReturn :: IsLine doc => LlvmCgConfig -> Maybe LlvmVar -> doc
ppReturn opts (Just var) = text "ret" <+> ppVar opts var
ppReturn _ nothing = text "ret" <+> ppLlvmType LMVoid
{-# SPECIALIZE ppReturn :: LlvmCgConfig -> Maybe LlvmVar -> SDoc #-}
{-# SPECIALIZE ppReturn :: LlvmCgConfig -> Maybe LlvmVar -> HLine #-}

ppBranch :: IsLine doc => LlvmCgConfig -> LlvmVar -> doc
ppBranch opts var = text "br" <+> ppVar opts var
{-# SPECIALIZE ppBranch :: LlvmCgConfig -> LlvmVar -> SDoc #-}
{-# SPECIALIZE ppBranch :: LlvmCgConfig -> LlvmVar -> HLine #-}

ppBranchIf :: IsLine doc => LlvmCgConfig -> LlvmVar -> LlvmVar -> LlvmVar -> doc
ppBranchIf opts cond trueT falseT
  = text "br" <+> ppVar opts cond <> comma <+> ppVar opts trueT <> comma <+> ppVar opts falseT
{-# SPECIALIZE ppBranchIf :: LlvmCgConfig -> LlvmVar -> LlvmVar -> LlvmVar -> SDoc #-}
{-# SPECIALIZE ppBranchIf :: LlvmCgConfig -> LlvmVar -> LlvmVar -> LlvmVar -> HLine #-}

ppPhi :: IsLine doc => LlvmCgConfig -> LlvmType -> [(LlvmVar, LlvmVar)] -> doc
ppPhi opts tp preds =
  let ppPreds (val, label) = brackets $ ppName opts val <> comma <+> ppName opts label
  in text "phi" <+> ppLlvmType tp <+> hsep (punctuate comma $ map ppPreds preds)
{-# SPECIALIZE ppPhi :: LlvmCgConfig -> LlvmType -> [(LlvmVar, LlvmVar)] -> SDoc #-}
{-# SPECIALIZE ppPhi :: LlvmCgConfig -> LlvmType -> [(LlvmVar, LlvmVar)] -> HLine #-}

ppSwitch :: IsDoc doc => LlvmCgConfig -> LlvmVar -> LlvmVar -> [(LlvmVar, LlvmVar)] -> doc
ppSwitch opts scrut dflt targets =
  let ppTarget (val, lab) = text "  " <> ppVar opts val <> comma <+> ppVar opts lab
  in lines_ $ concat
     [ [ text "switch" <+> ppVar opts scrut <> comma <+> ppVar opts dflt <+> char '[' ]
     , map ppTarget targets
     , [ char ']' ]
     ]
{-# SPECIALIZE ppSwitch :: LlvmCgConfig -> LlvmVar -> LlvmVar -> [(LlvmVar, LlvmVar)] -> SDoc #-}
{-# SPECIALIZE ppSwitch :: LlvmCgConfig -> LlvmVar -> LlvmVar -> [(LlvmVar, LlvmVar)] -> HDoc #-}

ppAsm
  :: IsLine doc
  => LlvmCgConfig -> LMString -> LMString -> LlvmType -> [LlvmVar] -> Bool -> Bool -> doc
ppAsm opts asm constraints rty vars sideeffect alignstack =
  let asm' = doubleQuotes $ ftext asm
      cons = doubleQuotes $ ftext constraints
      rty' = ppLlvmType rty
      vars' = lparen <+> ppCommaJoin (ppVar opts) vars <+> rparen
      side = if sideeffect then text "sideeffect" else empty
      align = if alignstack then text "alignstack" else empty
  in text "call" <+> rty' <+> text "asm" <+> side <+> align <+> asm' <> comma <+> cons <> vars'
{-# SPECIALIZE ppAsm :: LlvmCgConfig -> LMString -> LMString -> LlvmType -> [LlvmVar] -> Bool -> Bool -> SDoc #-}
{-# SPECIALIZE ppAsm :: LlvmCgConfig -> LMString -> LMString -> LlvmType -> [LlvmVar] -> Bool -> Bool -> HLine #-}

ppExtractV :: IsLine doc => LlvmCgConfig -> LlvmVar -> Int -> doc
ppExtractV opts struct idx =
  text "extractvalue"
  <+> ppLlvmType (getVarType struct) <+> ppName opts struct <> comma
  <+> int idx
{-# SPECIALIZE ppExtractV :: LlvmCgConfig -> LlvmVar -> Int -> SDoc #-}
{-# SPECIALIZE ppExtractV :: LlvmCgConfig -> LlvmVar -> Int -> HLine #-}

ppInsert :: IsLine doc => LlvmCgConfig -> LlvmVar -> LlvmVar -> LlvmVar -> doc
ppInsert opts vec elt ids =
  text "insertelement"
  <+> ppLlvmType (getVarType vec) <+> ppName opts vec <> comma
  <+> ppLlvmType (getVarType elt) <+> ppName opts elt <> comma
  <+> ppVar opts ids
{-# SPECIALIZE ppInsert :: LlvmCgConfig -> LlvmVar -> LlvmVar -> LlvmVar -> SDoc #-}
{-# SPECIALIZE ppInsert :: LlvmCgConfig -> LlvmVar -> LlvmVar -> LlvmVar -> HLine #-}

-- ppShuffle :: IsLine doc => LlvmCgConfig -> LlvmVar -> LlvmVar -> [Int] -> doc
-- ppShuffle opts v1 v2 idsx =
--   text "shufflevector"
--   <+> ppLlvmType (getVarType v1) <+> ppName opts v1 <> comma
--   <+> ppLlvmType (getVarType v2) <+> ppName opts v2 <> comma
--   <+> ppLlvmType (LMVec
-- ppShuffle :: LlvmCgConfig -> LlvmVar -> LlvmVar -> [Int] -> SDoc 

ppMetaAnnotExpr :: IsLine doc => LlvmCgConfig -> [MetaAnnot] -> LlvmExpression -> doc
ppMetaAnnotExpr opts meta expr =
  ppLlvmExpression opts expr <> ppMetaAnnots opts meta
{-# SPECIALIZE ppMetaAnnotExpr :: LlvmCgConfig -> [MetaAnnot] -> LlvmExpression -> SDoc #-}
{-# SPECIALIZE ppMetaAnnotExpr :: LlvmCgConfig -> [MetaAnnot] -> LlvmExpression -> HLine #-}

ppMetaAnnots :: IsLine doc => LlvmCgConfig -> [MetaAnnot] -> doc
ppMetaAnnots opts meta = hcat $ map ppMeta meta
  where
    ppMeta (MetaAnnot name e)
      = comma <+> exclamation <> ftext name <+>
        case e of
          MetaNode n -> ppMetaId n
          MetaStruct ms -> exclamation <> braces (ppCommaJoin (ppMetaExpr opts) ms)
          other -> exclamation <> braces (ppMetaExpr opts other)
{-# SPECIALIZE ppMetaAnnots :: LlvmCgConfig -> [MetaAnnot] -> SDoc #-}
{-# SPECIALIZE ppMetaAnnots :: LlvmCgConfig -> [MetaAnnot] -> HLine #-}

ppName :: IsLine doc => LlvmCgConfig -> LlvmVar -> doc
ppName opts v = case v of
  LMGlobalVar{} -> char '@' <> ppPlainName opts v
  LMLocalVar{} -> char '%' <> ppPlainName opts v
  LMNLocalVar{} -> char '%' <> ppPlainName opts v
  LMLitVar{} -> ppPlainName opts v
{-# SPECIALIZE ppName :: LlvmCgConfig -> LlvmVar -> SDoc #-}
{-# SPECIALIZE ppName :: LlvmCgConfig -> LlvmVar -> HLine #-}

ppPlainName :: IsLine doc => LlvmCgConfig -> LlvmVar -> doc
ppPlainName opts v = case v of
  LMGlobalVar x _ _ _ _ _ -> ftext x
  LMLocalVar x LMLabel -> pprUniqueAlways x
  LMLocalVar x _ -> char 'l' <> pprUniqueAlways x
  LMNLocalVar x _ -> ftext x
  LMLitVar x -> ppLit opts x
{-# SPECIALIZE ppPlainName :: LlvmCgConfig -> LlvmVar -> SDoc #-}
{-# SPECIALIZE ppPlainName :: LlvmCgConfig -> LlvmVar -> HLine #-}

ppLit :: IsLine doc => LlvmCgConfig -> LlvmLit -> doc
ppLit opts l = case l of
  LMIntLit i _ -> integer i
  LMFloatLit r LMFloat -> ppFloat (llvmCgPlatform opts) $ narrowFp r
  LMFloatLit r LMDouble -> ppDouble (llvmCgPlatform opts) r
  f@LMFloatLit{} -> pprPanic "ppList"
    (text "Can't print this float literal: " <> ppTypeLit opts f)
  LMNullLit _ -> text "null"
  -- LMUndefLit t
  --   | llvmCgFillUndefWithGarbage opts
  --   , Just lit <- garbageLit t -> ppLit opts lit
  --   | otherwise -> text "undef"
{-# SPECIALIZE ppLit :: LlvmCgConfig -> LlvmLit -> SDoc #-}
{-# SPECIALIZE ppLit :: LlvmCgConfig -> LlvmLit -> HLine #-}

ppVar :: IsLine doc => LlvmCgConfig -> LlvmVar -> doc
ppVar = ppVar' []
{-# SPECIALIZE ppVar :: LlvmCgConfig -> LlvmVar -> SDoc #-}
{-# SPECIALIZE ppVar :: LlvmCgConfig -> LlvmVar -> HLine #-}

ppVar' :: IsLine doc => [LlvmParamAttr] -> LlvmCgConfig -> LlvmVar -> doc
ppVar' attrs opts v = case v of
  LMLitVar x -> ppTypeLit' attrs opts x
  x -> ppLlvmType (getVarType x) <+> ppSpaceJoin ppLlvmParamAttr attrs <+> ppName opts x
{-# SPECIALIZE ppVar' :: [LlvmParamAttr] -> LlvmCgConfig -> LlvmVar -> SDoc #-}
{-# SPECIALIZE ppVar' :: [LlvmParamAttr] -> LlvmCgConfig -> LlvmVar -> HLine #-}

ppTypeLit :: IsLine doc => LlvmCgConfig -> LlvmLit -> doc
ppTypeLit = ppTypeLit' []
{-# SPECIALIZE ppTypeLit :: LlvmCgConfig -> LlvmLit -> SDoc #-}
{-# SPECIALIZE ppTypeLit :: LlvmCgConfig -> LlvmLit -> HLine #-}

ppTypeLit' :: IsLine doc => [LlvmParamAttr] -> LlvmCgConfig -> LlvmLit -> doc
ppTypeLit' attrs opts l = case l of
  -- LMVectorLitP{} -> panic "vectorlit"
  _ -> ppLlvmType (getLitType l) <+> ppSpaceJoin ppLlvmParamAttr attrs <+> ppLit opts l
{-# SPECIALIZE ppTypeLit' :: [LlvmParamAttr] -> LlvmCgConfig -> LlvmLit -> SDoc #-}
{-# SPECIALIZE ppTypeLit' :: [LlvmParamAttr] -> LlvmCgConfig -> LlvmLit -> HLine #-}

ppStatic :: IsLine doc => LlvmCgConfig -> LlvmStatic -> doc
ppStatic opts st = case st of
  LMComment s -> text "; " <> ftext s
  LMStaticLit l -> ppTypeLit opts l
  LMUninitType t -> ppLlvmType t <> text " undef"
  LMStaticStr s t -> ppLlvmType t <> text " c\"" <> ftext s <> text "\\00\""
  LMStaticArray d t -> ppLlvmType t <> text " [" <> ppCommaJoin (ppStatic opts) d <> char ']'
  LMStaticStructP d t -> ppLlvmType t <> text "<{" <> ppCommaJoin (ppStatic opts) d <> text "}>"
  LMStaticStructU d t -> ppLlvmType t <> text "{" <> ppCommaJoin (ppStatic opts) d <> text "}"
  LMStaticPointer v -> ppVar opts v
  LMTrunc v t -> ppLlvmType t <> text " trunc ("
                 <> ppStatic opts v <> text " to " <> ppLlvmType t <> char ')'
  LMBitc v t -> ppLlvmType t <> text " bitcast ("
                <> ppStatic opts v <> text " to " <> ppLlvmType t <> char ')'
  LMPtoI v t -> ppLlvmType t <> text " ptrtoint ("
                <> ppStatic opts v <> text " to " <> ppLlvmType t <> char ')'
  LMAdd s1 s2 -> pprStaticArith opts s1 s2 (text "add") (text "fadd") (text "LMAdd")
  LMSub s1 s2 -> pprStaticArith opts s1 s2 (text "sub") (text "fsub") (text "LMSub")
{-# SPECIALIZE ppStatic :: LlvmCgConfig -> LlvmStatic -> SDoc #-}
{-# SPECIALIZE ppStatic :: LlvmCgConfig -> LlvmStatic -> HLine #-}

pprSpecialStatic :: IsLine doc => LlvmCgConfig -> LlvmStatic -> doc
pprSpecialStatic opts stat = case stat of
  LMBitc v t -> panic "lmbitc"
  LMStaticPointer x -> ppLlvmType (pLower $ getVarType x)
  _ -> ppStatic opts stat
{-# SPECIALIZE pprSpecialStatic :: LlvmCgConfig -> LlvmStatic -> SDoc #-}
{-# SPECIALIZE pprSpecialStatic :: LlvmCgConfig -> LlvmStatic -> HLine #-}

pprStaticArith
  :: IsLine doc => LlvmCgConfig -> LlvmStatic -> LlvmStatic -> doc -> doc -> SDoc -> doc
pprStaticArith opts s1 s2 int_op float_op op_name =
  let ty1 = getStatType s1
      op = if isFloat ty1 then float_op else int_op
  in if ty1 == getStatType s2
     then ppLlvmType ty1 <+> op
          <+> lparen <> ppStatic opts s1 <> comma <> ppStatic opts s2 <> rparen
     else pprPanic "pprStaticArith" $
          op_name <> text " with different types! s1: " <> ppStatic opts s1
          <> text ", s2: " <> ppStatic opts s2
{-# SPECIALIZE pprStaticArith :: LlvmCgConfig -> LlvmStatic -> LlvmStatic -> SDoc -> SDoc -> SDoc -> SDoc #-}
{-# SPECIALIZE pprStaticArith :: LlvmCgConfig -> LlvmStatic -> LlvmStatic -> HLine -> HLine -> SDoc -> HLine #-}

--------------------------------------------------------------------------------
-- * Misc functions
--------------------------------------------------------------------------------

newLine :: IsDoc doc => doc
newLine = empty
{-# SPECIALIZE newLine :: SDoc #-}
{-# SPECIALIZE newLine :: HDoc #-}

exclamation :: IsLine doc => doc
exclamation = char '!'
{-# SPECIALIZE exclamation :: SDoc #-}
{-# SPECIALIZE exclamation :: HLine #-}
