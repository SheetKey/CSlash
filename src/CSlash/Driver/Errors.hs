{-# LANGUAGE ScopedTypeVariables #-}

module CSlash.Driver.Errors where

import CSlash.Driver.Errors.Types
import CSlash.Types.SourceError
import CSlash.Types.Error
import CSlash.Utils.Error
import CSlash.Utils.Outputable (hang, ppr, ($$),  text, mkErrStyle, sdocStyle, updSDocContext )
import CSlash.Utils.Logger

printMessages
  :: forall a. Diagnostic a => Logger -> DiagnosticOpts a -> DiagOpts -> Messages a -> IO ()
printMessages logger msg_opts opts msgs
  = sequence_ [ let style = mkErrStyle name_ppr_ctx
                    ctx = (diag_ppr_ctx opts) { sdocStyle = style }
                in logMsg logger (MCDiagnostic sev reason (diagnosticCode dia)) s $
                   updSDocContext (const ctx) (messageWithHints dia)
              | msg@MsgEnvelope { errMsgSpan = s
                                , errMsgDiagnostic = dia
                                , errMsgSeverity = sev
                                , errMsgReason = reason
                                , errMsgContext = name_ppr_ctx }
                  <- sortMsgBag (Just opts) (getMessages msgs)
              ]
  where
    messageWithHints :: Diagnostic a => a -> SDoc
    messageWithHints e =
      let main_msg = formatBulleted $ diagnosticMessage msg_opts e
      in case diagnosticHints e of
        [] -> main_msg
        [h] -> main_msg $$ hang (text "Suggested fix:") 2 (ppr h)
        hs -> main_msg $$ hang (text "Suggested fixes:") 2
                               (formatBulleted $ mkDecorated . map ppr $ hs)

printOrThrowDiagnostics :: Logger -> CsMessageOpts -> DiagOpts -> Messages CsMessage -> IO ()
printOrThrowDiagnostics logger print_config opts msgs
  | errorsOrFatalWarningsFound msgs
  = throwErrors msgs
  | otherwise
  = printMessages logger print_config opts msgs

mkDriverPsHeaderMessage :: MsgEnvelope PsMessage -> MsgEnvelope DriverMessage
mkDriverPsHeaderMessage = fmap DriverPsHeaderMessage
