{-# Language GeneralizedNewtypeDeriving #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}

module Thesis.Measure.Benchmark
    ( -- * Batch Parsing
      colateParseResults
    , gatherBenchmarkFileContents
      -- * User Informational Output
    , notifyParseFailure
    , notifyParseSuccess
    , notifyTaggedResult
    ) where

import Data.Foldable (traverse_, toList)
import Parser.BenchScript (BenchParameters)
import System.OsPath
import Thesis.Measure.Benchmark.File
import Thesis.Measure.Benchmark.Set


colateParseResults :: Foldable f => f (FilePathNoting BenchmarkFileContent) -> BenchmarkSeriesSet
colateParseResults = colateBenchmarkSeries . fmap getFileNote . toList


gatherBenchmarkFileContents :: Foldable f => f OsPath -> IO ([FilePathNoting BenchmarkFileParseError], [FilePathNoting BenchmarkFileContent])
gatherBenchmarkFileContents = fmap partitionFileNotes . traverse parseBenchmarkFileContent . toList


notifyParseFailure :: Foldable f => f (FilePathNoting BenchmarkFileParseError) -> IO ()
notifyParseFailure = outputFileList "FAILURE"


notifyParseSuccess :: Foldable f => f (FilePathNoting BenchmarkFileContent) -> IO ()
notifyParseSuccess = outputFileList "SUCCESS"


notifyTaggedResult :: Foldable f => f (FilePathNoting BenchmarkFileContent) -> IO ()
notifyTaggedResult ress = 
    let convert :: FilePathNoting BenchmarkFileContent -> FilePathNoting BenchParameters
        convert = fmap extractBenchmarkIndex

        indices :: [FilePathNoting BenchParameters]
        indices = convert <$> toList ress

        render :: Show a => FilePathNoting a -> String
        render x = unwords [ show $ getFileNote x, "=>", getFilePath x ] 

    in  outputList "Parsed benchmark series indices" render indices


outputFileList :: Foldable f => String -> f (FilePathNoting a) -> IO ()
outputFileList suff = outputList ("Files resulting in parse " <> suff) id . fmap getFilePath . toList


outputList :: Foldable f => String -> (a -> String) -> f a -> IO ()
outputList pref f xs =
            let size  = " (" <> show (length xs) <> "):"
                above = pref <> size
                fstIO = putStrLn above
                sndIO 
                    | null xs   = putStrLn "(None)"
                    | otherwise = traverse_ (\x -> putStr "\t" *> putStrLn (f x)) xs
            in  fstIO *> sndIO *> putChar '\n'
