module Main
( main
) where

import qualified Facet.Core.Type.Test
import           Hedgehog.Main

main :: IO ()
main = defaultMain
  [ Facet.Core.Type.Test.tests
  ]
