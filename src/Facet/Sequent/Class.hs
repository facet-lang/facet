{-# LANGUAGE FunctionalDependencies #-}
module Facet.Sequent.Class
( Term(..)
) where

import Data.Text (Text)
import Facet.Name (LName, Level, Name, RName)
import Facet.Pattern (Pattern)
import Facet.Syntax (Var, (:=:))

class Term term coterm command | coterm -> term command, term -> coterm command, command -> term coterm where
  -- Terms
  var :: Var (LName Level) -> term
  µR :: (coterm -> command) -> term
  funR :: [(Pattern Name, Pattern (Name :=: term) -> term)] -> term
  conR :: RName -> term
  stringR :: Text -> term
  dictR :: [RName :=: term] -> term
  compR :: [RName :=: Name] -> (Pattern (Name :=: term) -> term) -> term

  -- Coterms
  covar :: Var (LName Level) -> coterm
  µL :: (term -> command) -> coterm
  funL :: term -> coterm -> coterm

  -- Commands
  (|||) :: term -> coterm -> command

  infix 1 |||
