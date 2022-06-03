module Main
    ( main
    ) where

import Control.Exception (SomeException, displayException, try)
import Control.Monad.Except
import Data.Bifunctor (bimap, first)
import Data.String (IsString(..))
import Data.Text.Builder.Linear (runBuilder)
import Data.Text.IO (hGetContents, hPutStrLn, putStrLn)
import Data.Validation
import Prelude hiding (putStrLn)
--import Thesis.Batch.Mandate
import System.Environment (getArgs)
import System.IO (Handle, IOMode(ReadMode), hIsEOF, openFile, stderr, stdin)
import Thesis.Batch.Printer
import Thesis.Batch.Scanner


main :: IO ()
main = finalize $ do
    (source, handle) <- parseArgs
    stream           <- lift $ hGetContents handle
    config           <- liftEither . first show . toEither $ markdownScanner source stream
    lift $ putStrLn . runBuilder $ renderMarkdown config


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


finalize :: ExceptT String IO a -> IO ()
finalize computation = runExceptT computation >>= either (hPutStrLn stderr . fromString) (const $ pure ())
