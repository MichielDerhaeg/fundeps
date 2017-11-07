{-# LANGUAGE LambdaCase #-}

module Main
  ( main
  , runTest
  ) where

import           Backend.FcTypeChecker  (fcTypeCheck)
import           Frontend.HsParser      (hsParse)
import           Frontend.HsRenamer     (hsRename)
import           Frontend.HsTypeChecker (hsElaborate)

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
  case hsParse fileContents filePath of
    Left err     -> throwMainError "parser" err
    Right ps_pgm ->
      case hsRename us0 ps_pgm of
        Left err -> throwMainError "renamer" err
        Right (((rn_pgm, _rn_ctx), us1), rn_env) ->
          case hsElaborate rn_env us1 rn_pgm of
            Left err -> throwMainError "typechecker" err
            Right ((((fc_pgm, tc_ty, theory), envs), us2), _tc_env) ->
              case fcTypeCheck envs us2 fc_pgm of
                Left err -> do
                  throwMainError "System F typechecker" err
                  putStrLn $ renderWithColor $ ppr fc_pgm
                Right ((fc_ty, _us3), _fc_env) -> do
                  putStrLn "---------------------------- Elaborated Program ---------------------------"
                  putStrLn $ renderWithColor $ ppr fc_pgm
                  putStrLn "------------------------------- Program Type ------------------------------"
                  putStrLn $ renderWithColor $ ppr tc_ty
                  putStrLn "------------------------------ Program Theory -----------------------------"
                  putStrLn $ renderWithColor $ ppr theory
                  putStrLn "-------------------------- System F Program Type --------------------------"
                  putStrLn $ renderWithColor $ ppr fc_ty
  where
    throwMainError phase e
      | label <- colorDoc red (text phase <+> text "failure")
      , msg   <- brackets label <+> colorDoc red (text e)
      = putStrLn (renderWithColor msg)

