{-# Language GeneralizedNewtypeDeriving #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}

module Main
    ( main
    ) where

import Control.Monad ((<=<), filterM)
--import Data.ByteString.Lazy (hPut)
--import Data.Csv (encodeDefaultOrderedByName)
--import Data.Either (partitionEithers)
--import System.Environment (getArgs)
--import System.IO (hPutStr, stderr, stdout)
--import Thesis.Parser.Row
--import Data.Functor (void)
import Data.Bifunctor
import Data.Foldable (fold, traverse_, toList)
import Data.List (intersperse, isInfixOf, sort)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Semigroup (Arg(..))
import Data.Text.Lazy (Text)
import Data.Text.Lazy.IO (readFile)
--import Data.Tuple (swap)
--import Data.Validation
import Data.Void
--import Parser.Internal
--import Parser.SPIN.BackMatter
import Parser.BenchScript (BenchParameters, pBenchScript)
import Parser.SPIN.FrontMatter
import Parser.SPIN.RuntimeBody
--import Parser.SPIN.Types
import Prelude hiding (readFile)
import System.Environment (getArgs)
import Text.Megaparsec hiding (failure)

import Thesis.Benchmark.Set
import Thesis.Catalog.LTL
import Thesis.Catalog.Membership
import Thesis.Catalog.Protocol

import System.Directory.OsPath
import System.OsPath


main :: IO ()
main =
    getArgs >>= \case
        []   -> fail "Supply a file path"
        fp:_ -> do
            print beginIndex
            print finalIndex
            print <=< makeAbsolute <=< encodeFS $ fp
            searchDir <- canonicalizePath <=< encodeFS $ fp
            putStrLn . (\x -> "Gathering benchmarks from:\n\t" <> x <> "\n") <=< decodeFS $ searchDir
            benchmarkFiles <- sort <$> gatherInputPaths searchDir
--            traverse_ (putStrLn <=< decodeFS) benchmarkFiles
            printParseResult <=< gatherBenchmarkFileContents $ benchmarkFiles

--            parseTest pBenchmarkFileContent <=< readFile <=< decodeFS benchmarkFiles
--            void . pure . parse parser "" <=< readFile <=< decodeFS $ head benchmarkFiles


--parser :: Parsec Void Text (BenchScript, (RuntimeBody, BackMatter))
--parser = (,) <$> pBenchScript <*> (pFrontMatter *> pRuntimeBody)



gatherBenchmarkFileContents :: Foldable f => f OsPath -> IO ([Arg FilePath BenchmarkFileParseError], [Arg FilePath BenchmarkFileContent])
gatherBenchmarkFileContents = fmap partitionResults . traverse parseBenchmarkFileContent . toList


printParseResult :: Foldable f => (f (Arg FilePath BenchmarkFileParseError), f (Arg FilePath BenchmarkFileContent)) -> IO ()
printParseResult (errs, ress) =
    let getPath :: Arg FilePath a -> FilePath
        getPath (Arg fp _) = fp

        untag :: Arg a b -> b
        untag (Arg _ x) = x

        colateParseResults :: Foldable f => f (Arg FilePath BenchmarkFileContent) -> BenchmarkSeriesSet
        colateParseResults = colateBenchmarkSeries . fmap untag . toList

        outputList :: Foldable f => String -> (a -> String) -> f a -> IO ()
        outputList pref f xs =
            let size  = " (" <> show (length xs) <> "):"
                above = pref <> size
                fstIO = putStrLn above
                sndIO 
                    | null xs   = putStrLn "(None)"
                    | otherwise = traverse_ (\x -> putStr "\t" *> putStrLn (f x)) xs
            in  fstIO *> sndIO *> putChar '\n'

        failureIO :: IO ()
        failureIO = outputList "Files resulting in parse FAILURE" id $ getPath <$> toList errs

        successIO :: IO ()
        successIO = outputList "Files resulting in parse SUCCESS" id $ getPath <$> toList ress

        taggingIO :: IO ()
        taggingIO =
            let convert :: Arg FilePath BenchmarkFileContent -> Arg FilePath BenchParameters
                convert = fmap extractBenchmarkIndex

                indices :: [Arg FilePath BenchParameters]
                indices = convert <$> toList ress
                
                render :: Show a => Arg String a -> String
                render (Arg fp key) = unwords [ show key, "=>", fp ] 

            in  outputList "Parsed benchmark series indices" render indices

        benchSetIO :: IO () 
        benchSetIO = print $ colateParseResults ress

    in  failureIO *> successIO *> taggingIO *> benchSetIO


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
            let finalizer :: Either (ParseErrorBundle Text Void) c -> Arg FilePath (Either BenchmarkFileParseError c)
                finalizer = Arg fp . first makeBenchmarkFileParseError
                parser    = parse pBenchmarkFileContent fp
            in  finalizer . parser <$> readFile fp
    in  parseFile <=< decodeFS


pBenchmarkFileContent :: Parsec Void Text BenchmarkFileContent
pBenchmarkFileContent = do
    bs <- pBenchScript
    (rb, mbm) <- pFrontMatter *> pRuntimeBody
    pure $ BenchmarkFileContent bs rb mbm


newtype BenchmarkFileParseError = BenchmarkFileParseError (NonEmpty (ParseErrorBundle Text Void))
    deriving (Eq, Semigroup)


instance Show BenchmarkFileParseError where

    show (BenchmarkFileParseError errs) = unlines . intersperse "" $ errorBundlePretty <$> toList errs


makeBenchmarkFileParseError :: ParseErrorBundle Text Void -> BenchmarkFileParseError
makeBenchmarkFileParseError = BenchmarkFileParseError . pure


beginIndex :: (Protocol, LTL, Membership)
beginIndex = (Version1, FSU, 3)


finalIndex :: (Protocol, LTL, Membership)
finalIndex = (Version2, PCS, 8)


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
