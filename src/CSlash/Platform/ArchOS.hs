module CSlash.Platform.ArchOS where

data ArchOS = ArchOS
  { archOS_arch :: Arch
  , archOS_OS :: OS
  }
  deriving (Read, Show, Eq, Ord)

data Arch
  = ArchUnknown
  | ArchX86_64
  deriving (Read, Show, Eq, Ord)

data OS
  = OSUnknown
  | OSLinux
  deriving (Read, Show, Eq, Ord)

stringEncodeArch :: Arch -> String
stringEncodeArch arch = case arch of
  ArchUnknown -> "unknown"
  ArchX86_64 -> "x86_64"

stringEncodeOS :: OS -> String
stringEncodeOS os = case os of
  OSUnknown -> "unknown"
  OSLinux -> "linux"

osElfTarget :: OS -> Bool
osElfTarget OSLinux = True
osElfTarget OSUnknown = False
