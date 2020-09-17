{-# LANGUAGE ApplicativeDo #-}
module Facet.Examples
( prelude
) where

import Facet.Syntax

prelude :: Module expr ty decl mod => mod ()
prelude = do
  "id" .: forAll $ \ _A
    -> _A >-> \ x -> _A
    .= x
  "const" .: forAll $ \ _A -> forAll $ \ _B
    -> _A >-> \ x -> _B --> _A
    .= lam0 (const x)
  "unit" .: _Unit .= pure ()
  "flip" .: forAll $ \ _A -> forAll $ \ _B -> forAll $ \ _C
    -> (_A --> _B --> _C) >-> \ f -> _B >-> \ b -> _A >-> \ a -> _C
    .= f $$ a $$ b
  "curry" .: forAll $ \ _A -> forAll $ \ _B -> forAll $ \ _C
    -> ((_A .* _B) --> _C) >-> \ f -> _A >-> \ a -> _B >-> \ b -> _C
    .= f $$ ((,) <$> a <*> b)
  "curry" .: forAll $ \ _A -> forAll $ \ _B -> forAll $ \ _C
    -> (_A --> _B --> _C) >-> \ f -> _A .* _B >-> \ ab -> _C
    .= f $$ (fst <$> ab) $$ (snd <$> ab)
  pure ()
