{-# LANGUAGE ScopedTypeVariables #-}

module CSlash.Types.SourceError where

import CSlash.Types.Error
import CSlash.Utils.Monad
import CSlash.Utils.Panic
import CSlash.Utils.Exception
import CSlash.Utils.Error (pprMsgEnvelopeBagWithLocDefault)
import CSlash.Utils.Outputable

import CSlash.Driver.Errors.Ppr () -- instance Diagnostic CsMessage
import CSlash.Driver.Errors.Types

import Control.Monad.Catch as MC (MonadCatch, catch)

mkSrcErr :: Messages CsMessage -> SourceError
mkSrcErr = SourceError

throwErrors :: MonadIO io => Messages CsMessage -> io a
throwErrors = liftIO . throwIO . mkSrcErr

newtype SourceError = SourceError (Messages CsMessage)

instance Show SourceError where
  show (SourceError msgs) =
      renderWithContext defaultSDocContext
    . vcat
    . pprMsgEnvelopeBagWithLocDefault
    . getMessages
    $ msgs

instance Exception SourceError

handleSourceError :: (MonadCatch m) => (SourceError -> m a) -> m a -> m a
handleSourceError handler act = MC.catch act (\(e :: SourceError) -> handler e)
