{-# Language OverloadedStrings #-}

module Main
    ( main
    ) where

import Control.Exception (SomeException, displayException, try)
import Control.Monad.Except
import Data.Bifunctor (bimap, first)
import Data.Foldable
import Data.List (partition)
import Data.String (IsString(..))
import Data.Text (Text)
import Data.Text.IO (hGetContents, hPutStrLn, putStrLn)
import Data.Validation
import Prelude hiding (putStrLn, unlines)
import System.Environment (getArgs)
import System.Exit (ExitCode(..))
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
    result           <- lift $ invokeCluster `fulfills` config
    printProceeds result


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


printProceeds :: Foldable f => f InvokedOutput -> ExceptT String IO ()
printProceeds =
    let leftPaddedText :: (IsString s, Integral i, Show a) => i -> a -> s
        leftPaddedText m v =
            let s = show v
                n = length s
            in  fromString $ replicate (fromIntegral m - n) ' ' <> s

        countExitCodes :: Foldable f => f InvokedOutput -> (Int, Int)
        countExitCodes = bimap length length . partition (== ExitSuccess) . fmap exitCode . toList

        printExitCodes :: (Int, Int) -> IO ()
        printExitCodes (p,f) =
            let width = length . show $ max p f
                shown = leftPaddedText width
            in  putStrLn $ fold
                    [ "\n"
                    , "  PASS: ", shown p, "\n"
                    , "  FAIL: ", shown f, "\n"
                    , "\n"
                    ]
    in  lift . printExitCodes . countExitCodes
