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
  { qname         :: QName -> p
  , instantiation :: p -> p -> p
  }

verboseOptions :: Printer p => Options p
verboseOptions = Options
  { qname         = qualified
  , instantiation = printInstantiation
  }

quietOptions :: Printer p => Options p
quietOptions = Options
  { qname         = unqualified
  , instantiation = suppressInstantiation
  }

qualified, unqualified :: Printer p => QName -> p
qualified = pretty
unqualified = pretty . qlast

printInstantiation :: Printer p => p -> p -> p
printInstantiation = (<+>)

suppressInstantiation :: p -> p -> p
suppressInstantiation = const
