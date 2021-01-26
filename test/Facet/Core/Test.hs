{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Facet.Core.Test
( tests
) where

import Facet.Core
import Facet.Name
import Facet.Stack
import Facet.Syntax
import Hedgehog hiding (Var, eval)

tests :: IO Bool
tests = checkParallel $$(discover)

prop_quotation_inverse = property $ do
  let init = TForAll (Binding Im (Just (U "ε")) TInterface) (TForAll (Binding Im (Just (U "A")) TType) (TForAll (Binding Ex (Just (U "x")) (TVar (Free 0))) (TComp (Sig (TVar (Free 2)) []) (TVar (Free 1)))))
  quote 0 (eval Nil mempty init) === init
