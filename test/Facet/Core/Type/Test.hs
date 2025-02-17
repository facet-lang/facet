{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Facet.Core.Type.Test
( tests
) where

import Facet.Kind
import Facet.Name
import Facet.Quote
import Facet.Snoc
import Facet.Syntax
import Facet.Type.Expr
import Facet.Type.Norm (eval)
import Hedgehog hiding (Var, eval)

tests :: IO Bool
tests = checkParallel $$(discover)

prop_quotation_inverse = property $ do
  let init = ForAll (T "A") KType (Arrow (Just (T "x")) (Var (Bound (Right 0))) (Comp mempty (Var (Bound (Right 0)))))
  runQuoter 0 (quote (eval mempty Nil init)) === init
