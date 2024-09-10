module CSlash.Platform.ArchOS where

data ArchOS = ArchOS
  { archOS_arch :: Arch
  , archOS_OS :: OS
  }
  deriving (Show, Eq, Ord)

data Arch
  = ArchUnknown
  | ArchX86_64
  deriving (Show, Eq, Ord)

data OS
  = OSUnknown
  | OSLinux
  deriving (Show, Eq, Ord)
