{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE Safe #-}

module Thesis.Measure.Runtime
  ( Runtime()
  , fromPicoseconds
  , fromMilliseconds
  , fromMicroseconds
  , fromSeconds
  , toPicoseconds
  , toMicroseconds
  , toMilliseconds
  , toSeconds
  , timeDifference
  , timeOp
  , timeOpUT
  , timeOpCPUWall
  , timeSum
  ) where


import Control.DeepSeq
import Control.Monad.IO.Class
import Data.Foldable
import Data.Time.Clock
import Numeric.Natural
import System.CPUTime


-- | CPU time with picosecond resolution
newtype Runtime = Runtime Natural
    deriving (Eq, Ord)


instance NFData Runtime where

    rnf (Runtime !_) = ()


instance Show Runtime where

    show (Runtime x)
      | x < nSecond = let (q,_) = x `quotRem` 1       in fold [show q, ".", "???"                       , "ps" ]
      | x < μSecond = let (q,r) = x `quotRem` nSecond in fold [show q, ".", zeroPad 3 (r `div` 1       ), "ns" ]
      | x < mSecond = let (q,r) = x `quotRem` μSecond in fold [show q, ".", zeroPad 3 (r `div` nSecond ), "μs" ]
      | x <  second = let (q,r) = x `quotRem` mSecond in fold [show q, ".", zeroPad 3 (r `div` μSecond ), "ms" ]
      | x <  minute = let (q,r) = x `quotRem`  second in fold [show q, ".", zeroPad 3 (r `div` mSecond ), "s " ]
      | x <    hour = let (q,r) = x `quotRem`  minute in fold [show q, "m", zeroPad 2 (r `div`  second ), "sec"]
      | x <     day = let (q,r) = x `quotRem`    hour in fold [show q, "h", zeroPad 2 (r `div`  minute ), "min"]
      | otherwise   = let (q,r) = x `quotRem`     day in fold [show q, "d", zeroPad 2 (r `div`    hour ), "hrs"]
      where
        nSecond = 1000
        μSecond = 1000 * nSecond
        mSecond = 1000 * μSecond
        second  = 1000 * mSecond
        minute  = 60   *  second
        hour    = 60   *  minute
        day     = 24   *  hour


zeroPad :: Int -> Natural -> String
zeroPad k i = replicate (k - length shown) '0' <> shown
  where
    shown = show i


timeOp :: (MonadIO m, NFData a) => m a -> m (Runtime, a)
timeOp ioa = do
    t1 <- liftIO getCPUTime
    a  <- force <$> ioa
    t2 <- liftIO getCPUTime
    let t = Runtime . fromIntegral $ t2 - t1
    pure (t, a)

-- unit in pico second or something so not what I want in seconds
timeOpUT :: (MonadIO m, NFData a) => m a -> m (Runtime, a)
timeOpUT ioa = do
    t1 <- liftIO getCurrentTime
    a  <- force <$> ioa
    t2 <- liftIO getCurrentTime
    let picoMagnitude = 1000000000000 :: Integer
    let t = Runtime . fromIntegral $ picoMagnitude * (floor  (nominalDiffTimeToSeconds (diffUTCTime t2 t1)))
    pure (t, a)

-- reports both Runtime (ie total over parallel)  and wall clock duration
timeOpCPUWall :: (MonadIO m, NFData a) => m a -> m (Runtime, Runtime, a)
timeOpCPUWall ioa = do
    wt1 <- liftIO getCurrentTime
    ct1 <- liftIO getCPUTime
    a   <- force <$> ioa
    ct2 <- liftIO getCPUTime
    wt2 <- liftIO getCurrentTime
    let wt = (Runtime . fromIntegral) (1000000000000 * (floor  (nominalDiffTimeToSeconds (diffUTCTime wt2 wt1))) :: Integer)
    let ct = Runtime . fromIntegral $ ct2 - ct1
    pure (wt, ct, a)

timeDifference :: Runtime -> Runtime -> Runtime
timeDifference (Runtime a) (Runtime b) = Runtime $ max a b - min a b

timeSum :: Runtime -> Runtime -> Runtime
timeSum (Runtime a) (Runtime b) = Runtime $ a + b

fromPicoseconds :: Natural -> Runtime
fromPicoseconds = Runtime


fromMicroseconds :: Natural -> Runtime
fromMicroseconds = Runtime . (*1000000)


fromMilliseconds :: Natural -> Runtime
fromMilliseconds = Runtime . (*1000000000)


fromSeconds :: Natural -> Runtime
fromSeconds = Runtime . (*1000000000000)


toPicoseconds :: Runtime -> Natural
toPicoseconds (Runtime x) = x


toMicroseconds :: Runtime -> Natural
toMicroseconds (Runtime x) = x `div` 1000000


toMilliseconds :: Runtime -> Natural
toMilliseconds (Runtime x) = x `div` 1000000000


toSeconds :: Runtime -> Natural
toSeconds (Runtime x) = x `div` 1000000000000
