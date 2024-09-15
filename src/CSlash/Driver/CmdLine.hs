{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}

module CSlash.Driver.CmdLine where

import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Data.Bag
import CSlash.Types.SrcLoc
import CSlash.Types.Error
import CSlash.Utils.Error
import CSlash.Driver.Errors.Types
import CSlash.Driver.Errors.Ppr ()
import CSlash.Utils.Outputable (text)

import Data.Function
import Data.List (sortBy, intercalate, stripPrefix)
import Data.Word

import GHC.ResponseFile
import Control.Exception (IOException, catch)
import Control.Monad (ap)
import Control.Monad.IO.Class

--------------------------------------------------------
--         The Flag and OptKind types
--------------------------------------------------------

data Flag m = Flag
  { flagName :: String
  , flagOptKind :: OptKind m
  , flagCsMode :: CsFlagMode
  }

defFlag :: String -> OptKind m -> Flag m
defFlag name optKind = Flag name optKind AllModes

hoistFlag :: forall m n. (forall a. m a -> n a) -> Flag m -> Flag n
hoistFlag f (Flag a b c) = Flag a (go b) c
  where
    go (NoArg k) = NoArg (go2 k)
    go (HasArg k) = HasArg (\s -> go2 (k s))
    go (SepArg k) = SepArg (\s -> go2 (k s))
    go (Prefix k) = Prefix (\s -> go2 (k s))
    go (OptPrefix k) = OptPrefix (\s -> go2 (k s))
    go (OptIntSuffix k) = OptIntSuffix (\n -> go2 (k n))
    go (IntSuffix k) = IntSuffix (\n -> go2 (k n))
    go (Word64Suffix k) = Word64Suffix (\s -> go2 (k s))
    go (FloatSuffix k) = FloatSuffix (\s -> go2 (k s))
    go (PassFlag k) = PassFlag (\s -> go2 (k s))
    go (AnySuffix k) = AnySuffix (\s -> go2 (k s))

    go2 :: EwM m a -> EwM n a
    go2 (EwM g) = EwM $ \loc es ws -> f (g loc es ws)

data CsFlagMode
  = OnlyCs
  | AllModes
  | HiddenFlag

data OptKind m
  = NoArg (EwM m ())
  | HasArg (String -> EwM m ())
  | SepArg (String -> EwM m ())
  | Prefix (String -> EwM m ())
  | OptPrefix (String -> EwM m ())
  | OptIntSuffix (Maybe Int -> EwM m ())
  | IntSuffix (Int -> EwM m ())
  | Word64Suffix (Word64 -> EwM m ())
  | FloatSuffix (Float -> EwM m ())
  | PassFlag (String -> EwM m ())
  | AnySuffix (String -> EwM m ())

--------------------------------------------------------
--         The EwM monad
--------------------------------------------------------

newtype Err = Err { errMsg :: Located String }

type Warn = Located DriverMessage

type Errs = Bag Err

type Warns = [Warn]

newtype EwM m a = EwM { unEwM :: Located String -> Errs -> Warns -> m (Errs, Warns, a) }
  deriving (Functor)

instance Monad m => Applicative (EwM m) where
  pure v = EwM (\_ e w -> return (e, w, v))
  (<*>) = ap

instance Monad m => Monad (EwM m) where
  (EwM f) >>= k = EwM (\l e w -> do (e', w', r) <- f l e w
                                    unEwM (k r) l e' w')

instance MonadIO m => MonadIO (EwM m) where
  liftIO = liftEwM . liftIO

runEwM :: EwM m a -> m (Errs, Warns, a)
runEwM action = unEwM action (panic "processArgs: no arg yet") emptyBag mempty

setArg :: Located String -> EwM m () -> EwM m ()
setArg l (EwM f) = EwM (\_ es ws -> f l es ws)

addErr :: Monad m => String -> EwM m ()
addErr e = EwM (\(L loc _) es ws -> return (es `snocBag` Err (L loc e), ws, ()))

addWarn :: Monad m => String -> EwM m ()
addWarn msg = addFlagWarn $ DriverUnknownMessage $ mkSimpleUnknownDiagnostic $
  mkPlainDiagnostic WarningWithoutFlag noHints $ text msg

addFlagWarn :: Monad m => DriverMessage -> EwM m ()
addFlagWarn msg = EwM
  (\(L loc _) es ws -> return (es, L loc msg : ws, ()))

getArg :: Monad m => EwM m String
getArg = EwM (\(L _ arg) es ws -> return (es, ws, arg))

getCurLoc :: Monad m => EwM m SrcSpan
getCurLoc = EwM (\(L loc _) es ws -> return (es, ws, loc))

liftEwM :: Monad m => m a -> EwM m a
liftEwM action = EwM (\_ es ws -> do { r <- action; return (es, ws, r) })

warnsToMessages :: DiagOpts -> [Warn] -> Messages DriverMessage
warnsToMessages diag_opts = foldr
  (\(L loc w) ws -> addMessage (mkPlainMsgEnvelope diag_opts loc w) ws)
  emptyMessages

--------------------------------------------------------
--         Processing arguments
--------------------------------------------------------

processArgs
  :: Monad m
  => [Flag m]
  -> [Located String]
  -> (FilePath -> EwM m [Located String])
  -> m ([Located String], [Err], Warns)
processArgs spec args handleRespFile = do
  (errs, warns, spare) <- runEwM action
  return (spare, bagToList errs, warns)
  where
    action = process args []

    process [] spare = return (reverse spare)
    process (L _ ('@':resp_file) : args) spare = do
      resp_args <- handleRespFile resp_file
      process (resp_args ++ args) spare
    process (locArg@(L _ ('-':arg)) : args) spare = do
      case findArg spec arg of
        Just (rest, opt_kind) ->
          case processOneArg opt_kind rest arg args of
            Left err -> let b = process args spare
                        in (setArg locArg $ addErr err) >> b
            Right (action, rest) -> let b = process rest spare
                                    in (setArg locArg $ action) >> b
        Nothing -> process args (locArg : spare)
    process (arg : args) spare = process args (arg : spare)

processOneArg
  :: OptKind m -> String -> String -> [Located String]
  -> Either String (EwM m (), [Located String])
processOneArg opt_kind rest arg args
  = let dash_arg = '-' : arg
        rest_no_eq = dropEq rest
    in case opt_kind of
         NoArg a -> assert (null rest) Right (a, args)

         HasArg f | notNull rest_no_eq -> Right (f rest_no_eq, args)
                  | otherwise -> case args of
                                   [] -> missingArgErr dash_arg
                                   (L _ arg1:args1) -> Right (f arg1, args1)

         SepArg f -> case args of
                       [] -> missingArgErr dash_arg
                       (L _ arg1:args1) -> Right (f arg1, args1)

         Prefix f | notNull rest_no_eq -> Right (f rest_no_eq, args)
                  | otherwise -> Right (f dash_arg, args)

         OptIntSuffix f | null rest -> Right (f Nothing, args)
                        | Just n <- parseInt rest_no_eq -> Right (f (Just n), args)
                        | otherwise -> Left ("malformed integer argument in " ++ dash_arg)

         IntSuffix f | Just n <- parseInt rest_no_eq -> Right (f n, args)
                     | otherwise -> Left ("malformed integer argument in " ++ dash_arg)

         Word64Suffix f | Just n <- parseWord64 rest_no_eq -> Right (f n, args)
                        | otherwise -> Left ("malformed natural argument in " ++ dash_arg)

         FloatSuffix f | Just n <- parseFloat rest_no_eq -> Right (f n, args)
                       | otherwise -> Left ("malformed float argument in " ++ dash_arg)

         OptPrefix f -> Right (f rest_no_eq, args)

         AnySuffix f -> Right (f dash_arg, args)

findArg :: [Flag a] -> String -> Maybe (String, OptKind a)
findArg spec arg = case sortBy (compare `on` (length . fst))
                        [ (removeSpaces rest, optKind)
                        | flag <- spec
                        , let optKind = flagOptKind flag
                        , Just rest <- [stripPrefix (flagName flag) arg]
                        , arg_ok optKind rest arg ]
                   of
                     [] -> Nothing
                     (one:_) -> Just one

arg_ok :: OptKind t -> [Char] -> String -> Bool
arg_ok (NoArg _) rest _ = null rest
arg_ok (HasArg _) _ _ = True
arg_ok (SepArg _) rest _ = null rest
arg_ok (Prefix _) _ _ = True -- checked in processOneArg
arg_ok (OptIntSuffix _) _ _ = True
arg_ok (IntSuffix _) _ _ = True
arg_ok (Word64Suffix _) _ _ = True
arg_ok (FloatSuffix _) _ _ = True
arg_ok (OptPrefix _) _ _ = True
arg_ok (PassFlag _) rest _ = null rest
arg_ok (AnySuffix _) _ _ = True

parseInt :: String -> Maybe Int
parseInt s = case reads s of
               ((n, ""):_) -> Just n
               _ -> Nothing

parseWord64 :: String -> Maybe Word64
parseWord64 s = case reads s of
                  ((n, ""):_) -> Just n
                  _ -> Nothing

parseFloat :: String -> Maybe Float
parseFloat s = case reads s of
                 ((n, ""):_) -> Just n
                 _ -> Nothing

dropEq :: String -> String
dropEq ('=' : s) = s
dropEq s = s

unknownFlagErr :: String -> Either String a
unknownFlagErr f = Left ("unrecognized flag: " ++ f)

missingArgErr :: String -> Either String a
missingArgErr f = Left ("missing argument for flag: " ++ f)

parseResponseFile :: MonadIO m => FilePath -> EwM m [Located String]
parseResponseFile path = do
  res <- liftIO $ fmap Right (readFile path) `catch`
         \(e :: IOException) -> pure (Left e)
  case res of
    Left _err -> addErr "Could not open response file" >> return []
    Right resp_file -> return $ map (mkGeneralLocated path) (unescapeArgs resp_file)
