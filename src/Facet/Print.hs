{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Print
( prettyPrint
, UntypedPrint(..)
, Context(..)
, Print(..)
) where

import           Control.Applicative (Const(..), (<**>))
import           Control.Monad.IO.Class
import           Data.Coerce
import qualified Data.Kind as K
import           Facet.Pretty.Fresh
import           Facet.Pretty.Prec
import           Facet.Pretty.Rainbow
import           Facet.Syntax
import qualified Facet.Syntax.Untyped as U
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as ANSI

prettyPrint :: MonadIO m => Print sig a -> m ()
prettyPrint = prettyPrintWith defaultStyle

prettyPrintWith :: MonadIO m => (Nest Highlight -> ANSI.AnsiStyle) -> Print sig a -> m ()
prettyPrintWith style  = putDoc . PP.reAnnotate style . rainbow . runPrec Null . fresh . (`runUntypedPrint` const id) . runPrint . group

defaultStyle :: Nest Highlight -> ANSI.AnsiStyle
defaultStyle = \case
  Nest i   -> colours !! (getNesting i `mod` len)
  Ann Name -> mempty
  Ann Op   -> ANSI.color     ANSI.Cyan
  Ann Lit  -> ANSI.bold
  where
  colours =
    [ ANSI.Red
    , ANSI.Green
    , ANSI.Yellow
    , ANSI.Blue
    , ANSI.Magenta
    , ANSI.Cyan
    ]
    <**>
    [ANSI.color, ANSI.colorDull]
  len = length colours

type Inner = Fresh (Prec Context (Rainbow (PP.Doc (Nest Highlight))))
type Trans = Context -> Inner -> Inner

newtype UntypedPrint = UntypedPrint { runUntypedPrint :: Trans -> Inner }
  deriving (FreshPrinter (Nest Highlight), Monoid, Printer (Nest Highlight), Semigroup)

instance PrecPrinter Context (Nest Highlight) UntypedPrint where
  askingPrec = coerce (askingPrec :: (Context -> Trans -> Inner) -> Trans -> Inner)
  localPrec f (UntypedPrint run) = UntypedPrint $ \ t -> localPrec f (askingPrec (\ c -> t c (run t)))

context :: Context -> UntypedPrint -> UntypedPrint
context c a = UntypedPrint $ \ trans -> trans c (prec c (runUntypedPrint a trans))

withTransition :: (Context -> Inner -> Inner) -> UntypedPrint -> UntypedPrint
withTransition trans a = UntypedPrint $ \ _ -> runUntypedPrint a trans

whenPrec :: PrecPrinter lvl ann p => (lvl -> Bool) -> (p -> p) -> p -> p
whenPrec p f = ifPrec p f id

ifPrec :: PrecPrinter lvl ann p => (lvl -> Bool) -> (p -> p) -> (p -> p) -> p -> p
ifPrec p f g a = askingPrec $ \ p' -> if p p' then f a else g a


data Context
  = Null
  | FnR
  | FnL
  | Pattern
  | Expr
  | AppL
  | AppR
  | Var'
  deriving (Bounded, Eq, Ord, Show)

newtype Print (sig :: K.Type -> K.Type) a = Print { runPrint :: UntypedPrint }
  deriving (U.Err, U.Expr, FreshPrinter (Nest Highlight), Functor, Monoid, PrecPrinter Context (Nest Highlight), Printer (Nest Highlight), Semigroup, U.Type)
  deriving (Applicative) via Const UntypedPrint


data Highlight
  = Name
  | Op
  | Lit
  deriving (Enum, Eq, Ord, Show)

name :: Printer (Nest Highlight) doc => doc -> doc
name = annotate (Ann Name)

op :: Printer (Nest Highlight) doc => doc -> doc
op = annotate (Ann Op)


arrow :: Printer (Nest Highlight) doc => doc
arrow = op (pretty "->")


instance Expr Print where
  lam f = Print $ cases [\ var -> (var, coerce (f . Left) var)]
  ($$) = coerce app

  alg _ = Print $ pretty "TBD"

  weakenBy _ = coerce

cases :: [UntypedPrint -> (UntypedPrint, UntypedPrint)] -> UntypedPrint
cases cs = bind $ \ var -> whenPrec (/= Expr) (context Expr . group . align . braces . enclose (flatAlt space mempty) (flatAlt line mempty))
  . encloseSep
    mempty
    mempty
    (flatAlt (space <> comma <> space) (comma <> space))
  -- FIXME: how do we ensure that we add the arrow when anything _else_ (i.e. non-lambda) is printed?
  -- We could apply tht rule in everything else, or we could return the data back out in the printer
  -- Or maybe we could pass the arrow forward … somehow?
  -- CPS?
  $ map (\ (a, b) -> prec Pattern a <+> ifPrec (== Expr) (\ b -> arrow <> nest 2 (line <> b)) (prec Expr) b) (cs <*> [prettyVar var])

prettyVar :: Var -> UntypedPrint
prettyVar (Var i) = context Var' (name (pretty (alphabet !! r) <> if q > 0 then pretty q else mempty)) where
  (q, r) = i `divMod` 26
  alphabet = ['a'..'z']


instance U.Expr UntypedPrint where
  lam0 f = cases [\ var -> (var, f var)]
  lam  f = cases [\ var -> (var, f (Left var))]
  ($$) = app

  -- FIXME: don’t pretty-print local variables with the same name as globals used in the body
  global = pretty

  unit = pretty "()"
  l ** r = tupled [l, r]

instance U.Err UntypedPrint where
  err = pretty "err"

instance U.Type UntypedPrint where
  (-->) = infixr' FnL FnR (\ a b -> a <+> arrow <+> b)
  t >-> f = bind $ \ var -> let var' = prettyVar var in braces (space <> var' <+> colon <+> t <> space) <+> arrow <+> f var'
  (.$) = app
  l .* r = parens $ l <> comma <+> r
  _Unit = pretty "()"
  _Type = pretty "Type"
  tglobal = pretty


app :: UntypedPrint -> UntypedPrint -> UntypedPrint
app l r = context AppL $ op l r
  where
  op = infixl' AppL AppR $ \ f a -> askingPrec $ \case
    AppR -> f </> a
    _    -> f <> nest 2 (line <> a)
