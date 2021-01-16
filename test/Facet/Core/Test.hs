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
  let init = XTForAll (Binding Im (Just (U "ε")) XKInterface) (XTForAll (Binding Im (Just (U "A")) XKType) (XTForAll (Binding Ex (Just (U "x")) (XVar (Free 0))) (XTComp (Sig (XVar (Free 2)) []) (XVar (Free 1)))))
  quote 0 (eval Nil mempty init) === init
