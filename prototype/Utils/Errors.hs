{-# LANGUAGE FlexibleContexts #-}

module Utils.Errors where

import Utils.PrettyPrint
import Control.Monad.Except

-- GEORGE: Store a doc as an error, not a string
throwErrorM :: MonadError String m => Doc -> m a
throwErrorM d = throwError (renderError d)

data CompilePhase
  = HsParser
  | HsRenamer
  | HsTypeChecker
  | FcTypeChecker
  deriving (Show)

data CompileError = CompileError CompilePhase Doc

throwMainError (CompileError phase e) = putStrLn (renderWithColor msg)
  where
    label = colorDoc red (text (show phase) <+> text "failure")
    msg = brackets label <+> colorDoc red e
