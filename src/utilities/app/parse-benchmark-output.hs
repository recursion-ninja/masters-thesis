{-# Language GeneralizedNewtypeDeriving #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}

module Main
    ( main
    ) where

import Control.Monad ((<=<), filterM)
--import Data.ByteString.Lazy (hPut)
import Data.Csv (encodeDefaultOrderedByName)
--import Data.Either (partitionEithers)
--import System.Environment (getArgs)
--import System.IO (hPutStr, stderr, stdout)
--import Thesis.Parser.Row
--import Data.Functor (void)
import Data.ByteString.Lazy (writeFile)
import Data.Foldable (fold)
import Data.List (isInfixOf, sort)
import Prelude hiding (readFile, writeFile)
import System.Directory.OsPath
import System.Environment (getArgs)
import System.OsPath
import Thesis.Measure.Benchmark
import Thesis.Measure.Benchmark.Set (BenchmarkSeriesSet, extractRowsForCSV)


main :: IO ()
main =
    getArgs >>= \case
        []   -> fail "Supply a file path"
        fp:_ -> do
            print <=< makeAbsolute <=< encodeFS $ fp
            searchDir <- canonicalizePath <=< encodeFS $ fp
            putStrLn . (\x -> "Gathering benchmarks from:\n\t" <> x <> "\n") <=< decodeFS $ searchDir
            benchmarkFiles <- sort <$> gatherInputPaths searchDir
--            traverse_ (putStrLn <=< decodeFS) benchmarkFiles

            (errs, ress) <- gatherBenchmarkFileContents $ benchmarkFiles
            notifyParseFailure errs
            notifyParseSuccess ress
            notifyTaggedResult ress

            let benchSet = colateParseResults ress
            writeOutCSV defaultCSV benchSet

            print benchSet


defaultCSV :: FilePath
defaultCSV = "benchmarking-measurements.csv"


writeOutCSV :: FilePath -> BenchmarkSeriesSet -> IO ()
writeOutCSV path = writeFile path . encodeDefaultOrderedByName . extractRowsForCSV


gatherInputPaths :: OsPath -> IO [OsPath]
gatherInputPaths =
  let benchmarkOutput :: (OsPath -> IO Bool)
      benchmarkOutput =
          let isSlurmFile  :: OsPath -> IO Bool
              isSlurmFile  = fmap ("slurm" `isInfixOf`) . decodeFS . takeBaseName
              
              isOutputFile :: OsPath -> IO Bool
              isOutputFile fp = (== takeExtension fp) <$> encodeFS ".out"
              
          in  \fp -> (&&) <$> isOutputFile fp <*> isSlurmFile fp
  in  (benchmarkOutput `locateFilesWithin`)


locateFilesWithin :: (OsPath -> IO Bool) -> OsPath -> IO [OsPath]
locateFilesWithin desiderata searchPath =
    let locate :: OsPath -> IO [OsPath]
        locate inPath = gather . fmap (inPath </>) <=< listDirectory $ inPath

        gather :: [OsPath] -> IO [OsPath]
        gather contents = do
          (files, dirs) <- segregate contents
          keepFiles <- filterM desiderata files
          let merge = (keepFiles <>) . fold
          merge <$> traverse locate dirs

        segregate :: [OsPath] -> IO ([OsPath], [OsPath])
        segregate fps = (,)
            <$> filterM doesFileExist fps
            <*> filterM doesDirectoryExist fps

        fileOrDirectory path = doesFileExist path >>= \case
            True  -> pure $ pure path
            False -> sort <$> locate path

    in  fileOrDirectory searchPath


--parser :: Parsec Void Text (BenchScript, (RuntimeBody, BackMatter))
--parser = (,) <$> pBenchScript <*> (pFrontMatter *> pRuntimeBody)
{-

gatherBenchmarkFileContents :: Foldable f => f OsPath -> IO ([Arg FilePath BenchmarkFileParseError], [Arg FilePath BenchmarkFileContent])
gatherBenchmarkFileContents = fmap partitionResults . traverse parseBenchmarkFileContent . toList


colateParseResults :: Foldable f => f (Arg FilePath BenchmarkFileContent) -> BenchmarkSeriesSet
colateParseResults = colateBenchmarkSeries . fmap untag . toList


notifyParseFailure :: Foldable f => f (Arg FilePath BenchmarkFileParseError) -> IO ()
notifyParseFailure = outputFileList "FAILURE"


notifyParseSuccess :: Foldable f => f (Arg FilePath BenchmarkFileContent) -> IO ()
notifyParseSuccess = outputFileList "SUCCESS"


notifyTaggedResult :: Foldable f => f (Arg FilePath BenchmarkFileContent) -> IO ()
notifyTaggedResult ress = 
    let convert :: Arg FilePath BenchmarkFileContent -> Arg FilePath BenchParameters
        convert = fmap extractBenchmarkIndex

        indices :: [Arg FilePath BenchParameters]
        indices = convert <$> toList ress

        render :: Show a => Arg String a -> String
        render (Arg fp key) = unwords [ show key, "=>", fp ] 

    in  outputList "Parsed benchmark series indices" render indices


getTag :: Arg FilePath a -> FilePath
getTag (Arg fp _) = fp


untag :: Arg a b -> b
untag (Arg _ x) = x


outputFileList :: Foldable f => String -> f (Arg FilePath a) -> IO ()
outputFileList suff = outputList ("Files resulting in parse " <> suff) id . fmap getTag . toList


outputList :: Foldable f => String -> (a -> String) -> f a -> IO ()
outputList pref f xs =
            let size  = " (" <> show (length xs) <> "):"
                above = pref <> size
                fstIO = putStrLn above
                sndIO 
                    | null xs   = putStrLn "(None)"
                    | otherwise = traverse_ (\x -> putStr "\t" *> putStrLn (f x)) xs
            in  fstIO *> sndIO *> putChar '\n'


partitionResults
  :: Foldable f
  => f (Arg FilePath (Either BenchmarkFileParseError BenchmarkFileContent))
  -> ([Arg FilePath BenchmarkFileParseError], [Arg FilePath BenchmarkFileContent])
partitionResults =
    let consider :: Arg a (Either b c) -> ([Arg a b], [Arg a c]) -> ([Arg a b], [Arg a c])
        consider (Arg fp x) (es, rs) = case x of
            Left  err -> (Arg fp err : es, rs)
            Right res -> (es, Arg fp res : rs)
    in  bimap sort sort . foldr consider (mempty, mempty)


parseBenchmarkFileContent :: OsPath -> IO (Arg FilePath (Either BenchmarkFileParseError BenchmarkFileContent))
parseBenchmarkFileContent = 
    let parseFile fp =
            let finalizer :: NFData c => Either (ParseErrorBundle Text Void) c -> Arg FilePath (Either BenchmarkFileParseError c)
                finalizer = force . Arg fp . first makeBenchmarkFileParseError
                parser    = force . parse pBenchmarkFileContent fp
            in  withFile fp ReadMode (fmap (finalizer . parser . force) . hGetContents)
    in  parseFile <=< decodeFS


pBenchmarkFileContent :: Parsec Void Text BenchmarkFileContent
pBenchmarkFileContent = do
    bs <- pBenchScript
    (rb, mbm) <- pFrontMatter *> pRuntimeBody
    pure $ BenchmarkFileContent bs rb mbm


makeBenchmarkFileParseError :: ParseErrorBundle Text Void -> BenchmarkFileParseError
makeBenchmarkFileParseError = BenchmarkFileParseError . pure


beginIndex :: (Protocol, LTL, Membership)
beginIndex = (Version1, FSU, 3)


finalIndex :: (Protocol, LTL, Membership)
finalIndex = (Version2, PCS, 8)


-}
