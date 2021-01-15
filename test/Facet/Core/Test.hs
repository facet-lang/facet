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
  let init = TForAll (Binding Im (Just (U "ε")) KInterface) (TForAll (Binding Im (Just (U "A")) KType) (TForAll (Binding Ex (Just (U "x")) (Var (Free 0))) (TComp (Sig (Var (Free 2)) []) (Var (Free 1)))))
  quote 0 (eval Nil mempty init) === init
