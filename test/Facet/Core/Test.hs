{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Facet.Core.Test
( tests
) where

import Facet.Core
import Facet.Name
import Facet.Stack
import Facet.Syntax
import Hedgehog hiding (eval)

tests :: IO Bool
tests = checkParallel $$(discover)

prop_quotation_inverse = property $ do
  let init = QTSusp (QComp [Binding Im (Just (U "ε")) Nothing QKInterface, Binding Im (Just (U "A")) Nothing QKType, Binding Ex (Just (U "x")) Nothing (QVar (Free 0)) ] (Sig (QVar (Free 2)) []) (QVar (Free 1)))
  quote 0 (eval Nil mempty init) === init
