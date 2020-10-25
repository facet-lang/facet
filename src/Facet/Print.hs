{-# LANGUAGE TypeFamilies #-}
module Facet.Print
( getPrint
, Print(..)
, Precedence(..)
, Highlight(..)
, ann
  -- * Algebras
, Algebra(..)
, surface
, explicit
  -- * Core printers
, printValue
, printModule
) where

import           Data.Bifunctor
import           Data.Foldable (foldl', toList)
import           Data.Maybe (fromMaybe)
import           Data.Semigroup (stimes)
import qualified Data.Text as T
import           Data.Traversable (mapAccumL)
import qualified Facet.Core as C
import           Facet.Name
import           Facet.Pretty (lower, upper)
import           Facet.Stack
import           Facet.Syntax
import qualified Prettyprinter as PP
import           Silkscreen as P
import           Silkscreen.Printer.Prec hiding (Level)
import qualified Silkscreen.Printer.Prec as P
import           Silkscreen.Printer.Rainbow as P

getPrint :: Print -> PP.Doc Highlight
getPrint = runRainbow (annotate . Nest) 0 . runPrec Null . doc . group


data Print = Print { fvs :: FVs, doc :: Prec Precedence (Rainbow (PP.Doc Highlight)) }

instance Semigroup Print where
  Print v1 d1 <> Print v2 d2 = Print (v1 <> v2) (d1 <> d2)
  stimes n (Print v d) = Print (stimes n v) (stimes n d)

instance Monoid Print where
  mempty = Print mempty mempty

instance Vars Print where
  cons l d = Print (cons l (fvs d)) (doc d)
  bind l d = Print (bind l (fvs d)) (doc d)

instance Printer Print where
  type Ann Print = Highlight

  liftDoc0 a = Print mempty (liftDoc0 a)
  liftDoc1 f (Print v d) = Print v (liftDoc1 f d)
  liftDoc2 f (Print v1 d1) (Print v2 d2) = Print (v1 <> v2) (liftDoc2 f d1 d2)

  -- FIXME: these run everything twice which seems bad.
  -- but then again, laziness.
  column    f = Print (fvs (f 0))         (column    (doc . f))
  nesting   f = Print (fvs (f 0))         (nesting   (doc . f))
  pageWidth f = Print (fvs (f Unbounded)) (pageWidth (doc . f))

  enclosing (Print vl dl) (Print vr dr) (Print vx dx) = Print (vl <> vr <> vx) (enclosing dl dr dx)

  brackets (Print v d) = Print v (brackets d)
  braces   (Print v d) = Print v (braces   d)
  parens   (Print v d) = Print v (parens   d)
  angles   (Print v d) = Print v (angles   d)
  squotes  (Print v d) = Print v (squotes  d)
  dquotes  (Print v d) = Print v (dquotes  d)

instance PrecedencePrinter Print where
  type Level Print = Precedence

  -- FIXME: this is running things twice.
  askingPrec f = Print (fvs (f minBound)) (askingPrec (doc . f))
  localPrec f (Print v d) = Print v (localPrec f d)

instance Show Print where
  showsPrec p = showsPrec p . getPrint


data Precedence
  = Null
  | Ann
  | FnR
  | FnL
  | Comp
  | Expr
  | Pattern
  | AppL
  | AppR
  | Var
  deriving (Bounded, Eq, Ord, Show)

data Highlight
  = Nest Int
  | Name Level
  | Con
  | Type
  | Op
  | Lit
  | Hole Meta
  deriving (Eq, Show)

op :: (Printer p, Ann p ~ Highlight) => p -> p
op = annotate Op


arrow :: (Printer p, Ann p ~ Highlight) => p
arrow = op (pretty "->")

comp :: Print -> Print
comp
  = block
  . prec Comp

block :: Print -> Print
block
  = group
  . align
  . braces
  . enclose space space

commaSep :: [Print] -> Print
commaSep = encloseSep mempty mempty (comma <> space)

ann :: (PrecedencePrinter p, P.Level p ~ Precedence) => (p ::: p) -> p
ann (n ::: t) = align . prec Ann $ n </> group (align (colon <+> flatAlt space mempty <> t))


($$), (-->) :: Print -> Print -> Print
f $$ a = askingPrec $ \case
  AppL -> op
  _    -> group op
  where
  -- FIXME: lambdas get parenthesized on the left
  op = leftAssoc AppL AppR (\ f a -> f <> nest 2 (line <> a)) f a

(-->) = rightAssoc FnR FnL (\ a b -> group (align a) </> arrow <+> b)

($$*) :: Foldable t => Print -> t Print -> Print
($$*) = fmap group . foldl' ($$)

(>~>) :: ((Pl, Print) ::: Print) -> Print -> Print
((pl, n) ::: t) >~> b = prec FnR (flatAlt (column (\ i -> nesting (\ j -> stimes (j + 3 - i) space))) mempty <> group (align (unPl braces parens pl (space <> ann (setPrec Var n ::: t) <> line))) </> arrow <+> b)


-- Algebras

data Var
  = Global (Maybe MName) DName
  | TLocal UName Level
  | Local UName Level
  | Metavar Meta
  | Cons UName

qvar :: QName -> Var
qvar (m :.: n) = Global (Just m) n

data Algebra p = Algebra
  { var :: Var -> p
  , tintro :: UName -> Level -> p
  , intro :: UName -> Level -> p
  , lam
    :: [p] -- the clauses.
    -> p
  , clause
    :: [Pl_ (p ::: Maybe p)] -- the patterns.
    -> p                     -- the body.
    -> p
  , fn
    :: [Pl_ ([p] ::: p)] -- the argument types/bindings
    -> p                 -- the return type
    -> p
  , app :: p -> Stack (Pl_ p) -> p
  , hole :: UName -> p
  , _Type :: p
  , _Interface :: p
  , tcomp :: [p] -> p -> p
  , ann' :: (p ::: p) -> p
  , case' :: p -> [(p, p)] -> p -- ^ will only arise in core
  , pcon     :: p -> Stack p -> p
  , peff     :: p -> Stack p -> p -> p
  , tuple    :: [p] -> p
  , decl :: p ::: p -> p
  , defn :: p :=: p -> p
  , data' :: [p] -> p
  , module_ :: MName ::: Maybe p :=: ([p], [p]) -> p
  , import' :: MName -> p
  }


printVar :: ((Int -> Print) -> UName -> Level -> Print) -> Var -> Print
printVar name = \case
  Global _ n -> setPrec Var (pretty n)
  TLocal n d -> name upper n d
  Local  n d -> name lower n d
  Metavar  m -> setPrec Var (annotate (Hole m) (pretty '?' <> upper (getMeta m)))
  Cons     n -> setPrec Var (annotate Con (pretty n))

surface :: Algebra Print
surface = Algebra
  { var = printVar name
  , tintro = name upper
  , intro = name lower
  , lam = comp . embed . commaSep
  , clause = \ ns b -> embed (setPrec Pattern (vsep (map (unPl_ (braces . tm) tm) ns)) </> arrow) </> b
  -- FIXME: group quantifiers by kind again.
  , fn = flip (foldr (\ (P pl (n ::: _T)) b -> case n of
    [] -> _T --> b
    _  -> ((pl, group (commaSep n)) ::: _T) >~> b))
  , app = \ f as -> group f $$* fmap (group . unPl_ braces id) as
  , hole = \ n -> annotate (Hole (Meta 0)) $ pretty '?' <> pretty n
  , _Type = annotate Type $ pretty "Type"
  , _Interface = annotate Type $ pretty "Interface"
  , tcomp = \ s t -> case s of
    [] -> t
    _  -> brackets (commaSep s) <+> t
  , ann' = group . tm
  , case' = \ s ps -> align . group $ pretty "case" <+> setPrec Expr s </> block (concatWith (surround (hardline <> comma <> space)) (map (group . (\ (p, b) -> align (embed (prec Pattern p </> arrow) </> b))) ps))
  , pcon = \ n ps -> parens (hsep (annotate Con n:toList ps))
  , peff = \ n ps k -> brackets (hsep (annotate Con n:toList ps) <+> semi <+> k)
  , tuple = tupled
  , decl = ann
  , defn = \ (a :=: b) -> group a <> hardline <> group b
  , data' = block . group . concatWith (surround (hardline <> comma <> space)) . map group
  , module_ = \ (n ::: t :=: (is, ds)) -> ann (setPrec Var (pretty n) ::: fromMaybe (pretty "Module") t) </> concatWith (surround hardline) (is ++ map (hardline <>) ds)
  , import' = \ n -> pretty "import" <+> braces (enclose mempty mempty (setPrec Var (pretty n)))
  }
  where
  embed = nest 2 . group
  name f n d = setPrec Var . annotate (Name d) $ if T.null (getUName n) then
    pretty '_' <> f (getLevel d)
  else
    pretty n

-- FIXME: elide unused vars
explicit :: Algebra Print
explicit = surface
  { var = printVar name
  , tintro = name upper
  , intro = name lower
  , clause = \ ns b -> group (align (setPrec Pattern (vsep (map (\ (P pl (n ::: _T)) -> group $ unPl braces id pl (maybe n (ann . (n :::)) _T)) ns)) </> arrow)) </> b
  }
  where
  name f _ d = setPrec Var (annotate (Name d) (cons d (f (getLevel d))))


-- Core printers

printValue :: Algebra Print -> Stack Print -> C.Value -> Print
printValue alg = go
  where
  go env = \case
    C.VType -> _Type alg
    C.VInterface -> _Interface alg
    C.VForAll t b ->
      let (vs, (_, b')) = splitr C.unForAll' (d, C.VForAll t b)
          binding env (C.Binding p n s _T) =
            let _T' = (if null s then id else tcomp alg (map (delta env) (toList s))) (go env _T)
            in  (env :> tvar env (P p n ::: _T'), P p (name p n (Level (length env)) ::: _T'))
          name p n d
            | T.null (getUName n)
            , Ex <- p             = []
            | otherwise           = [tintro alg n d]
          (env', vs') = mapAccumL binding env vs
      in fn alg vs' (go env' b')
    C.VLam n b ->
      let (vs, (_, b')) = splitr C.unLam' (d, C.VLam n b)
          binding env (C.Binding p n s _T) =
            let _T' = (if null s then id else tcomp alg (map (delta env) (toList s))) (go env _T)
            in  (env :> lvar env (P p n ::: _T'), P p (unPl (tintro alg) (intro alg) p n (Level (length env)) ::: Just _T'))
          (env', vs') = mapAccumL binding env vs
      in lam alg [clause alg vs' (go env' b')]
    -- FIXME: there’s no way of knowing if the quoted variable was a type or expression variable
    -- FIXME: should maybe print the quoted variable differently so it stands out.
    C.VNeut h e ->
      let elim h sp  Nil     = case sp Nil of
            Nil -> h
            sp  -> app alg h sp
          elim h sp  (es:>e) = case e of
            C.EApp a   -> elim h (sp . (:> fmap (go env) a)) es
            C.ECase ps -> case' alg (elim h id es) (map clause ps)
          h' = C.unVar (ann' alg . bimap (var alg . qvar) (go env)) ((env !) . getIndex . levelToIndex d) (ann' alg . bimap (var alg . Metavar) (go env)) h
          clause (p, b) =
            let ((env', p'), v) = pat env p
            in (p', go env' (b v))
      in elim h' id e
    C.VCon (C.Con n p) -> app alg (ann' alg (bimap (var alg . qvar) (go env) n)) (fmap (ex . go env) p)
    where
    d = Level (length env)
  tvar env n = ann' alg (var alg (TLocal (out (tm n)) (Level (length env))) ::: ty n)
  lvar env n = ann' alg (var alg (unPl_ TLocal Local (tm n) (Level (length env))) ::: ty n)
  delta env (C.Delta (q ::: _T) sp) = app alg (ann' alg (var alg (qvar q) ::: go env _T)) (ex . go env <$> sp)

  pat env = \case
    C.PVar n    -> let { d = Level (length env) ; v = ann' alg (var alg (Local (tm n) d) ::: go env (ty n)) } in ((env :> v, v), C.PVar (C.free d))
    C.PCon (C.Con n ps) ->
      let ((env', p'), ps') = subpatterns env ps
      in ((env', pcon alg (ann' alg (bimap (var alg . qvar) (go env) n)) p'), C.PCon (C.Con n ps'))
  subpatterns env ps = mapAccumL (\ (env', ps) p -> let ((env'', v), p') = pat env' p in ((env'', ps:>v), p')) (env, Nil) ps

printModule :: Algebra Print -> C.Module -> Print
printModule alg (C.Module mname is _ ds) = module_ alg
  $   mname
  ::: Just (var alg (Global (Just (MName (T.pack "Kernel"))) (T (UName (T.pack "Module")))))
  :=: (map (\ (C.Import n) -> import' alg n) is, map def ds)
  where
  def (n, Nothing ::: t) = decl alg
    $   var alg (Global (Just mname) n)
    ::: printValue alg Nil t
  def (n, Just d  ::: t) = decl alg
    $   var alg (Global (Just mname) n)
    ::: defn alg (printValue alg Nil t
    :=: case d of
      C.DTerm b  -> printValue alg Nil b
      C.DData cs -> data' alg
        $ map (\ (n :=: _ ::: _T) -> decl alg (var alg (Cons n) ::: printValue alg Nil _T)) cs)
