module Facet.REPL
( repl
) where

import Control.Carrier.Readline.Haskeline

repl :: IO ()
repl = runReadlineWithHistory loop

loop :: Has Readline sig m => m ()
loop = pure ()
