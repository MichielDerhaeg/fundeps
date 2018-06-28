{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE UndecidableInstances   #-} -- should be fine

module Utils.Errors where

import Utils.PrettyPrint

import Control.Monad.Except

throwErrorM :: MonadError CompileError m => Doc -> m a
throwErrorM = throwError . CompileError Unknown

data CompilePhase
  = HsParser
  | HsRenamer
  | HsTypeChecker
  | FcTypeChecker
  | Unknown
  deriving (Show)

data CompileError = CompileError CompilePhase Doc

-- | Like Control.Monad.Fail but bettter
class Monad m => MonadFail m where
  failM :: CompileError -> m a

instance MonadFail Maybe where
  failM _ = Nothing

instance MonadFail (Either CompileError) where
  failM = Left

instance (Monad m, MonadError CompileError m) => MonadFail m where
  failM = throwError

throwMainError :: CompileError -> IO ()
throwMainError (CompileError phase e) = putStrLn (renderWithColor msg)
  where
    label = colorDoc red (text (show phase) <+> text "failure")
    msg = brackets label $$ e

markErrorPhase :: MonadError CompileError m => CompilePhase -> m a -> m a
markErrorPhase phase f =
  f `catchError`
  (\(CompileError _phase err) -> throwError (CompileError phase err))

tcFail :: MonadError CompileError m => Doc -> m a
tcFail = throwError . CompileError HsTypeChecker

markTcError :: MonadError CompileError m => m a -> m a
markTcError = markErrorPhase HsTypeChecker

tagError :: MonadError CompileError m => Doc -> m a -> m a
tagError doc f =
  f `catchError` \(CompileError phase err) ->
    throwError (CompileError phase (err $$ doc))
