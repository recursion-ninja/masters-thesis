{-# Language OverloadedStrings #-}

module Main
    ( main
    ) where

import Control.Exception (SomeException, displayException, try)
import Control.Monad.Except
import Data.Bifunctor (bimap, first)
import Data.Foldable
import Data.String (IsString(..))
import Data.Text (Text)
import Data.Text.IO (hGetContents, hPutStrLn, putStrLn)
import Data.Validation
import Prelude hiding (putStrLn, unlines)
import System.Environment (getArgs)
import System.IO (Handle, IOMode(ReadMode), hIsEOF, openFile, stderr, stdin)
import Thesis.Batch.Invoker
import Thesis.Batch.Mandate
import Thesis.Batch.Scanner


main :: IO ()
main = finalize $ do
    (source, handle) <- parseArgs
    stream           <- lift $ hGetContents handle
    config           <- liftEither . first show . toEither $ markdownScanner source stream
    printPreamble source config
    lift . void $ invokeCluster `fulfills` config


finalize :: ExceptT String IO a -> IO ()
finalize computation = runExceptT computation >>= either (hPutStrLn stderr . fromString) (const $ pure ())


parseArgs :: ExceptT String IO (FilePath, Handle)
parseArgs = do
    args             <- lift getArgs
    res@(name, hand) <- case args of
        [] -> pure ("STDIN", stdin)
        x : _ ->
            let safeOpenFile :: IO (Either SomeException Handle) -> IO (Either String (FilePath, Handle))
                safeOpenFile = fmap (bimap displayException (x, ))
            in  ExceptT . safeOpenFile . try $ openFile x ReadMode
    none <- lift $ hIsEOF hand
    when none . throwError $ name <> ": Empty input stream"
    pure res


printPreamble :: FilePath -> BatchMandate -> ExceptT String IO ()
printPreamble path =
    let prefix :: Word -> Text
        prefix n = fold
            [ "Mandate specification successfully parsed from:\n"
            , "\n"
            , "  "
            , fromString path
            , "\n"
            , "\n"
            , "\n"
            , "Batch configuration size:\n"
            , "\n"
            , "  "
            , fromString $ show n
            , " jobs\n"
            , "\n"
            , "\n"
            , "Sending batch to cluster...\n"
            , "\n"
            ]
    in  lift . putStrLn . prefix . cardinality
