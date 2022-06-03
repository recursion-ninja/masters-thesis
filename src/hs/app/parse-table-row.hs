module Main
    ( main
    ) where

import Control.Monad (when)
import Data.ByteString.Lazy (hPut)
import Data.Csv (encodeDefaultOrderedByName)
import Data.Either (partitionEithers)
import System.Environment (getArgs)
import System.IO (hPutStr, stderr, stdout)
import Thesis.Parser.Row


main :: IO ()
main = do
    logFiles <- getArgs
    when (null logFiles) $ fail "No log files provided"

    (errs, rows) <- partitionEithers <$> traverse extractRowFromFile logFiles

    hPutStr stderr $ unlines errs
    hPut stdout $ encodeDefaultOrderedByName rows
