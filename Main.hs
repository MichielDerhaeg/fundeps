{-# LANGUAGE LambdaCase #-}

module Main
  ( main
  , runTest
  ) where

import           Frontend.HsParser      (hsParse)
import           Frontend.HsRenamer     (hsRename)
import           Frontend.HsTypeChecker (hsElaborate)

import           Backend.FcSimplify     (fcSimplify)
import           Backend.FcTypeChecker  (fcTypeCheck)

import           Utils.Errors
import           Utils.PrettyPrint
import           Utils.Unique           (newUniqueSupply)

import           System.Environment     (getArgs, getProgName)

main :: IO ()
main =
  getArgs >>= \case
    [filename] -> runTest filename
    _other -> do
      progName <- getProgName
      putStrLn $ concat ["Usage: ", progName, " <filename>"]

-- | Run a single testfile
runTest :: FilePath -> IO ()
runTest filePath = do
  us0 <- newUniqueSupply 'u'
  fileContents <- readFile filePath
  let result = do
        ps_pgm <- hsParse fileContents filePath
        (((rn_pgm, _rn_ctx), us1), rn_env) <- hsRename us0 ps_pgm
        ((fc_pgm, us2), _tc_env) <-
          hsElaborate rn_env us1 rn_pgm
        (((), _us3), _fc_env) <- fcTypeCheck us2 fc_pgm
        let simpl_pgm = fcSimplify fc_pgm
        return simpl_pgm
  case result of
    Left err -> throwMainError err
    Right fc_pgm -> do
      putStrLn
        "---------------------------- Elaborated Program ---------------------------"
      putStrLn $ renderWithColor $ ppr fc_pgm
