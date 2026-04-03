module CSlash.Core.Seq where

import CSlash.Core as Core
import CSlash.Types.Var.Id.Info
import CSlash.Types.Demand( seqDemand, seqDmdSig )
-- import GHC.Types.Cpr( seqCprSig )
import CSlash.Types.Basic( seqOccInfo )
import CSlash.Types.Tickish
import CSlash.Types.Var.Set( seqDVarSet )
import CSlash.Types.Var( varType, varKind )
import CSlash.Core.Type( seqType, seqTyCo )
import CSlash.Core.Kind( seqKind, seqKiCo )
import CSlash.Types.Var.Id( idInfo )

megaSeqIdInfo :: IdInfo -> ()
megaSeqIdInfo info
  = seqDemand (demandInfo info) `seq`
    seqDmdSig (dmdSigInfo info) `seq`
    seqCaf (cafInfo info) `seq`
    seqOneShot (oneShotInfo info) `seq`
    seqOccInfo (occInfo info)

seqOneShot :: OneShotInfo -> () 
seqOneShot l = l `seq` ()

seqCaf :: CafInfo -> ()
seqCaf c = c `seq` ()

seqExpr :: CoreExpr -> ()
seqExpr (Var v) = v `seq` ()
seqExpr (Lit lit) = lit `seq` ()
seqExpr (App f a) = seqExpr f `seq` seqExpr a
seqExpr (Lam b k e) = seqCoreBndr b `seq` seqMKind k `seq` seqExpr e
seqExpr (Let b e) = seqBind b `seq` seqExpr e
seqExpr (Case e b t as) = seqExpr e `seq` seqLetBndr b `seq` seqType t `seq` seqAlts as
seqExpr (Cast e co) = seqExpr e `seq` seqTyCo co
seqExpr (Tick n e) = seqTickish n `seq` seqExpr e
seqExpr (Type t) = seqType t
seqExpr (KiCo co) = seqKiCo co
seqExpr (Kind ki) = seqKind ki

seqMKind :: Maybe CoreMonoKind -> ()
seqMKind (Just ki) = seqKind ki
seqMKind Nothing = ()

seqTickish :: CoreTickish -> ()
seqTickish CpcTick{} = ()

seqCoreBndr :: CoreBndr -> ()
seqCoreBndr (Core.Id id) = seqType (varType id) `seq` megaSeqIdInfo (idInfo id)
seqCoreBndr (Tv tv) = seqKind (varKind tv)
seqCoreBndr (KCv kcv) = seqKind (varKind kcv)
seqCoreBndr (Kv _) = ()

seqLetBndr :: CoreId -> ()
seqLetBndr id = seqType (varType id) `seq` megaSeqIdInfo (idInfo id)

seqLetBndrs :: [CoreId] -> ()
seqLetBndrs [] = ()
seqLetBndrs (b:bs) = seqLetBndr b `seq` seqLetBndrs bs

seqBinds :: [CoreBind] -> ()
seqBinds bs = foldr (seq . seqBind) () bs

seqBind :: CoreBind -> ()
seqBind (NonRec b e) = seqLetBndr b `seq` seqExpr e
seqBind (Rec prs) = seqPairs prs

seqPairs :: [(CoreId, CoreExpr)] -> ()
seqPairs [] = ()
seqPairs ((b, e) : prs) = seqLetBndr b `seq` seqExpr e `seq` seqPairs prs

seqAlts :: [CoreAlt] -> ()
seqAlts [] = ()
seqAlts (Alt c bs e : alts) = c `seq` seqLetBndrs bs `seq` seqExpr e `seq` seqAlts alts
