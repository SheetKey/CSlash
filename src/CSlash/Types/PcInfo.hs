module CSlash.Types.PcInfo where

data PcInfo
  = PcInfo
    { pcInfoTickCount :: Int
    , pcInfoHash :: Int
    }
  | NoPcInfo
    { pcUsed :: AnyPcUsage
    }

type AnyPcUsage = Bool
