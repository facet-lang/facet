{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Facet.Core.Type.Test
( tests
) where

import Facet.Core.Type
import Facet.Name
import Facet.Snoc
import Facet.Syntax
import Hedgehog hiding (Var, eval)

tests :: IO Bool
tests = checkParallel $$(discover)

prop_quotation_inverse = property $ do
  let init = TForAll (N "A") TType (TForAll (N "x") (TVar (Free 0)) (TComp [] (TVar (Free 1))))
  quote 0 (eval mempty Nil init) === init
