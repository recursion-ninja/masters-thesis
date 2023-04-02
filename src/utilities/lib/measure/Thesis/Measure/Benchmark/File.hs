{-# Language DeriveAnyClass #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}

module Thesis.Measure.Benchmark.File
    ( BenchmarkFileContent(..)
    , BenchmarkFileParseError(..)
    , FilePathNoting()
      -- ** Accessors
    , getFilePath
    , getFileNote
      -- ** Constructor
    , notedBy
      -- * Parsing functions
    , parseBenchmarkFileContent
    , partitionFileNotes
    ) where

import Control.DeepSeq (NFData, force)
import Control.Monad ((<=<))
import Data.Bifunctor
import Data.Foldable (toList)
import Data.List (intersperse, sort)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Semigroup (Arg(..))
import Data.Text (Text)
import Data.Text.IO (hGetContents)
import Data.Void
import GHC.Generics (Generic)
import Parser.BenchScript
import Parser.SPIN
import Prelude hiding (readFile)
import System.IO (IOMode(ReadMode), withFile)
import System.OsPath
import Text.Megaparsec hiding (failure)


{- |
General input type from file parser.
-}
data  BenchmarkFileContent
    = BenchmarkFileContent
    { extractedBenchScript :: BenchScript
    , extractedRuntimeBody :: RuntimeBody
    , extractedBackMatter  :: Maybe BackMatter
    } deriving (Show)


newtype BenchmarkFileParseError = BenchmarkFileParseError (NonEmpty (ParseErrorBundle Text Void))
    deriving newtype (Eq, Semigroup)


newtype FilePathNoting a = FilePathNoting (Arg FilePath a)
    deriving newtype (Eq, Ord)


deriving newtype instance Functor FilePathNoting


deriving stock instance Generic BenchmarkFileContent


deriving stock instance Generic BenchmarkFileParseError


deriving stock instance Generic a => Generic (FilePathNoting a)


deriving anyclass instance NFData BenchmarkFileContent


deriving anyclass instance NFData BenchmarkFileParseError


deriving anyclass instance (Generic a, NFData a) => NFData (FilePathNoting a)


instance Show BenchmarkFileParseError where

    show (BenchmarkFileParseError errs) = unlines . intersperse "" $ errorBundlePretty <$> toList errs


instance Show a => Show (FilePathNoting a) where

    show (FilePathNoting (Arg key val)) = unwords [ key, "=>", show val ]


getFilePath :: FilePathNoting a -> FilePath
getFilePath (FilePathNoting (Arg fp _)) = fp


getFileNote :: FilePathNoting a -> a
getFileNote (FilePathNoting (Arg _ x)) = x


notedBy :: FilePath -> a -> FilePathNoting a
notedBy fp = FilePathNoting . Arg fp


partitionFileNotes
  :: Foldable f
  => f (FilePathNoting (Either BenchmarkFileParseError BenchmarkFileContent))
  -> ([FilePathNoting BenchmarkFileParseError], [FilePathNoting BenchmarkFileContent])
partitionFileNotes =
    let consider :: FilePathNoting (Either b c) -> ([FilePathNoting b], [FilePathNoting c]) -> ([FilePathNoting b], [FilePathNoting c])
        consider (FilePathNoting (Arg filePath x)) (es, rs) =
            let build :: a -> FilePathNoting a
                build = (filePath `notedBy`)
            in  case x of
                  Left  err -> (build err : es, rs)
                  Right res -> (es, build res : rs)
    in  bimap sort sort . foldr consider (mempty, mempty)


parseBenchmarkFileContent :: OsPath -> IO (FilePathNoting (Either BenchmarkFileParseError BenchmarkFileContent))
parseBenchmarkFileContent =
    let parseFile fp =
            let finalizer :: NFData c => Either (ParseErrorBundle Text Void) c -> FilePathNoting (Either BenchmarkFileParseError c)
                finalizer = force . FilePathNoting . Arg fp . first makeBenchmarkFileParseError
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
