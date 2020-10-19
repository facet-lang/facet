module Main
( main
) where

import qualified Facet.Carrier.Parser.Church.Test
import qualified Facet.Source.Test
import           Hedgehog.Main

main :: IO ()
main = defaultMain
  [ Facet.Carrier.Parser.Church.Test.tests
  , Facet.Source.Test.tests
  ]
