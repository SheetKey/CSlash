module CSlash.Tc.Types where

{- *********************************************************************
*                                                                      *
                Global typechecker environment
*                                                                      *
********************************************************************* -}

data FrontendResult = FrontendTypecheck TcGblEnv

data TcGblEnv
