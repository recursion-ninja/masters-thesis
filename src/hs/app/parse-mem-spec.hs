{-# Language OverloadedStrings #-}

module Main
    ( main
    ) where

import Control.Exception (SomeException, displayException, try)
import Control.Monad.Except
import Data.Foldable
import Data.List (intersperse)
import Data.Bifunctor (bimap, first)
import Data.String (IsString(..))
import Data.Text.Builder.Linear (Builder, runBuilder)
import Data.Text (unlines)
import Data.Text.IO (hGetContents, hPutStrLn, putStrLn)
import Data.Validation
import Prelude hiding (putStrLn, unlines)
import Thesis.Batch.Mandate
import System.Environment (getArgs)
import System.IO (Handle, IOMode(ReadMode), hIsEOF, openFile, stderr, stdin)
import Thesis.Batch.Printer
import Thesis.Batch.Scanner


main :: IO ()
main = finalize $ do
    (source, handle) <- parseArgs
    stream           <- lift $ hGetContents handle
    config           <- liftEither . first show . toEither $ markdownScanner source stream
    lift . putStrLn . runBuilder $ renderMarkdown config
    lift . putStrLn . unlines  . fmap (fromString . show) . toList $ domain config
    lift . void $ printMorphism `fulfills` config


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


printMorphism :: Parameterized -> Specification -> IO ()
printMorphism (ltl, row, col) (minDFA, limMEM, lenVEC) =
    let renders :: (IsString a, Monoid a) => [a] -> a
        renders ks = "( " <> fold (intersperse ", " ks) <> " )"
        txtKeys = renders [ renderCell    ltl, renderCell    row, renderCell    col ] :: Builder
        txtVals = renders [ renderCell minDFA, renderCell limMEM, renderCell lenVEC ] :: Builder
    in  putStrLn . runBuilder $ fold [ "  ", txtKeys, "    -->    ", txtVals ]


finalize :: ExceptT String IO a -> IO ()
finalize computation = runExceptT computation >>= either (hPutStrLn stderr . fromString) (const $ pure ())
