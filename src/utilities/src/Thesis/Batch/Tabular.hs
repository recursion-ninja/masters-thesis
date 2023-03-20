module Thesis.Batch.Tabular
    ( -- * Type-class for tabular indexing
      Bounding (..)
    , NumericTable (..)
    , NumericTableSet (..)
      -- * Type-classes
    , Tabular (..)
      -- * Accessors
    , collectNumericTable
    , collectionOfLTLs
    ) where

import Thesis.Batch.Tabular.Bounding
import Thesis.Batch.Tabular.Class
import Thesis.Batch.Tabular.Numeric
