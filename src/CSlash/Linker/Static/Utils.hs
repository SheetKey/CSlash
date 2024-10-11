{-# LANGUAGE MultiWayIf #-}

module CSlash.Linker.Static.Utils where

import CSlash.Platform
import System.FilePath

progFileName :: ArchOS -> Bool -> Maybe FilePath -> FilePath
progFileName (ArchOS arch os) staticLink output_fn
  | Just s <- output_fn = if
      | staticLink -> s <?.> "a"
      | otherwise -> s
  | otherwise = if
      | staticLink -> "liba.a"
      | otherwise -> "a.out"
  where s <?.> ext | null (takeExtension s) = s <.> ext
                   | otherwise = s
