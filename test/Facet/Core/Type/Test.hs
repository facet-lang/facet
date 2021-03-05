{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Facet.Core.Type.Test
( tests
) where

import Facet.Core.Type
import Facet.Name
import Facet.Semiring
import Facet.Snoc
import Facet.Syntax
import Hedgehog hiding (Var, eval)

tests :: IO Bool
tests = checkParallel $$(discover)

prop_quotation_inverse = property $ do
  let init = TForAll (N "A") Type (TThunk (TArrow (Just (N "x")) zero (TVar (Free 0)) (TComp [] (TVar (Free 0)))))
  quoteP 0 (evalP mempty Nil init) === init
