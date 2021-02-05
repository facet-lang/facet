{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Facet.Core.Type.Test
( tests
) where

import Facet.Core.Type
import Facet.Name
import Facet.Stack
import Hedgehog hiding (Var, eval)

tests :: IO Bool
tests = checkParallel $$(discover)

prop_quotation_inverse = property $ do
  let init = TForAll (U "A") TType (TForAll (U "x") (TVar (TFree 0)) (TSusp [] (TVar (TFree 1))))
  quote 0 (eval mempty Nil init) === init
