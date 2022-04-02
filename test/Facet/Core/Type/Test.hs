{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Facet.Core.Type.Test
( tests
) where

import Facet.Env
import Facet.Kind
import Facet.Name
import Facet.Quote
import Facet.Semiring
import Facet.Syntax
import Facet.Type.Expr
import Facet.Type.Norm (eval)
import Hedgehog hiding (Var, eval)

tests :: IO Bool
tests = checkParallel $$(discover)

prop_quotation_inverse = property $ do
  let init = ForAll (T "A") KType (Arrow (Just (T "x")) Many (Var (Free (Right (LName 0 (T "A"))))) (Comp mempty (Var (Free (Right (LName 0 (T "A")))))))
  runQuoter 0 (quote (eval mempty empty init)) === init
