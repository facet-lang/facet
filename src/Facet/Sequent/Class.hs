{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Sequent.Class
( -- * Term abstraction
  Term(..)
  -- * Commands
, (:|:)(..)
) where

import Data.Text (Text)
import Facet.Name (LName, Level, Name, RName)
import Facet.Pattern (Pattern)
import Facet.Quote (Quote(..))
import Facet.Syntax (Var, (:=:))

-- * Term abstraction

class Term term coterm | coterm -> term, term -> coterm where
  -- Terms
  var :: Var (LName Level) -> term
  µR :: Name -> (coterm -> term :|: coterm) -> term
  funR :: [(Pattern Name, Pattern (Name :=: term) -> term)] -> term
  conR :: RName -> [term] -> term
  stringR :: Text -> term
  dictR :: [RName :=: term] -> term
  compR :: [RName :=: Name] -> (Pattern (Name :=: term) -> term) -> term

  -- Coterms
  covar :: Var (LName Level) -> coterm
  µL :: Name -> (term -> term :|: coterm) -> coterm
  funL :: term -> coterm -> coterm

  -- Commands
  (|||) :: term -> coterm -> term :|: coterm

  infix 1 |||


-- * Commands

data term :|: coterm = term :|: coterm

instance (Quote term1 term2, Quote coterm1 coterm2) => Quote (term1 :|: coterm1) (term2 :|: coterm2) where
  quote d (term :|: coterm) = quote d term :|: quote d coterm
