module Facet.Carrier.Fail.Throw.Print
( FailC(..)
) where

newtype FailC m a = FailC { runFail :: m a }
