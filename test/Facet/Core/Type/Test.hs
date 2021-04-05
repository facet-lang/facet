{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Facet.Core.Type.Test
( tests
) where

import Facet.Env
import Facet.Kind
import Facet.Name
import Facet.Semiring
import Facet.Syntax
import Facet.Type.Expr
import Facet.Type.Norm
import Hedgehog hiding (Var, eval)

tests :: IO Bool
tests = checkParallel $$(discover)

prop_quotation_inverse = property $ do
  let init = TForAll (U "A") KType (TArrow (Just (U "x")) Many (TVar (Free (Right (LName 0 (U "A"))))) (TComp mempty (TVar (Free (Right (LName 0 (U "A")))))))
  quote 0 (eval mempty empty init) === init
