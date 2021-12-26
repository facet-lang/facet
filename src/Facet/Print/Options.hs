module Facet.Print.Options
( -- * Options
  Options(..)
, verboseOptions
, quietOptions
, qualified
, unqualified
, printInstantiation
, suppressInstantiation
) where

import Facet.Name
import Silkscreen

-- Options

-- FIXME: add an option to control whether shifts are printed
data Options p = Options
  { rname         :: RName -> p
  , instantiation :: p -> p -> p
  }

verboseOptions :: Printer p => Options p
verboseOptions = Options
  { rname         = qualified
  , instantiation = printInstantiation
  }

quietOptions :: Printer p => Options p
quietOptions = Options
  { rname         = unqualified
  , instantiation = suppressInstantiation
  }

qualified, unqualified :: Printer p => RName -> p
qualified = pretty
unqualified (_:.:n) = pretty n

printInstantiation :: Printer p => p -> p -> p
printInstantiation = (<+>)

suppressInstantiation :: p -> p -> p
suppressInstantiation = const