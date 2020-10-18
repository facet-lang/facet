{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Algebra
( -- * Folds
  Var(..)
, Algebra(..)
, foldCValue
, foldCModule
, foldSType
, foldSExpr
, foldSCons
, foldSDecl
, foldSModule
) where

import           Data.Bifunctor (bimap)
import           Data.Foldable (toList)
import qualified Data.Text as T
import           Data.Traversable (mapAccumL)
import qualified Facet.Core as C
import           Facet.Name
import           Facet.Stack
import qualified Facet.Surface as S
import           Facet.Syntax
import           Text.Parser.Position

data Var
  = Global (Maybe MName) DName
  | TLocal UName Level
  | Local UName Level
  | Quote UName Level
  | Metavar Meta
  | Cons CName

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
    :: [Pl_ (Maybe p ::: p)] -- the argument types/bindings
    -> p                     -- the return type
    -> p
  , app :: p -> Stack (Pl_ p) -> p
  , prd :: [p] -> p
  , hole :: T.Text -> p
  , _Type :: p
  , _Void :: p
  , ann' :: (p ::: p) -> p
  , case' :: p -> [(p, p)] -> p -- ^ will only arise in core
  , wildcard :: p
  , pcon     :: p -> Stack p -> p
  , tuple    :: [p] -> p
  , decl :: p ::: p -> p
  , defn :: p :=: p -> p
  , data' :: [p] -> p
  , module_ :: MName ::: Maybe p :=: [p] -> p
  }


foldCValue :: Algebra p -> Level -> C.Value p -> p
foldCValue alg = go
  where
  go d = \case
    C.Type  -> _Type alg
    t C.:=> b  ->
      let (vs, (d', b')) = splitr (C.unForAll' tvar) (d, t C.:=> b)
      in fn alg (map (\ (d, n ::: _T) -> let n' = if T.null (getUName (out n)) then Nothing else Just (tintro alg (out n) d) in P (pl n) (n' ::: go d _T)) vs) (go d' b')
    C.Lam n b  ->
      let (vs, (d', b')) = splitr (C.unLam' lvar) (d, C.Lam n b)
      in lam alg [clause alg (map (\ (d, n) -> P (pl (tm n)) (unPl tintro intro (pl (tm n)) alg (out (tm n)) d ::: Just (go d (ty n)))) vs) (go d' b')]
    -- FIXME: there’s no way of knowing if the quoted variable was a type or expression variable
    -- FIXME: should maybe print the quoted variable differently so it stands out.
    C.Neut h e ->
      let elim h sp  Nil     = case sp Nil of
            Nil -> h
            sp  -> app alg h sp
          elim h sp  (es:>e) = case e of
            C.App a   -> elim h (sp . (:> fmap (go d) a)) es
            C.Case ps -> case' alg (elim h id es) (map clause ps)
          h' = C.unHead (ann' alg . bimap (var alg . qvar) (go d)) id (var alg . Quote __) (ann' alg . bimap (var alg . Metavar) (go d)) h
          clause (p, b) =
            let ((d', p'), v) = pat d p
            in (p', go d' (b v))
      in elim h' id e
    C.TPrd l r -> prd alg [go d l, go d r]
    C.Prd  l r -> prd alg [go d l, go d r]
    C.VCon n p -> app alg (ann' alg (bimap (var alg . qvar) (go d) n)) (fmap (ex . go d) p)
  tvar d n = ann' alg (var alg (TLocal (out (tm n)) d) ::: go d (ty n))
  lvar d n = ann' alg (var alg (unPl_ TLocal Local (tm n) d) ::: go d (ty n))

  pat d = \case
    C.Wildcard -> ((d, wildcard alg), C.Wildcard)
    C.Var n    -> let v = ann' alg (var alg (Local (tm n) d) ::: go d (ty n)) in ((succ d, v), C.Var (C.free v))
    C.Con n ps ->
      let ((d', p'), ps') = subpatterns d ps
      in ((d', pcon alg (ann' alg (bimap (var alg . qvar) (go d) n)) p'), C.Con n ps')
    C.Tuple ps ->
      let ((d', p'), ps') = subpatterns d ps
      in ((d', tuple alg (toList p')), C.Tuple ps')
  subpatterns d ps = mapAccumL (\ (d', ps) p -> let ((d'', v), p') = pat d' p in ((d'', ps:>v), p')) (d, Nil) ps

foldCModule :: Algebra p -> C.Module p -> p
foldCModule alg (C.Module n ds) = module_ alg
  $   n
  ::: Just (var alg (Global (Just (MName (T.pack "Kernel"))) (T (TName (UName (T.pack "Module"))))))
  :=: map def ds
  where
  def (m :.: n, d ::: t) = decl alg
    $   var alg (Global (Just m) n)
    ::: defn alg (foldCValue alg (Level 0) t
    :=: case d of
      C.DTerm b  -> foldCValue alg (Level 0) b
      C.DType b  -> foldCValue alg (Level 0) b
      C.DData cs -> data' alg
        $ map (decl alg . bimap (var alg . Cons) (foldCValue alg (Level 0))) cs)


foldSType :: Algebra p -> Stack p -> Spanned (S.Type a) -> p
foldSType alg = go
  where
  go env (s, t) = case t of
    S.TFree n  -> var alg (Global Nothing n)
    S.TBound n -> env ! getIndex n
    S.THole n  -> hole alg n
    S.Type     -> _Type alg
    t S.:=> b ->
      let (ts, b') = splitr (S.unForAll . snd) (s, t S.:=> b)
          ((_, env'), ts') = mapAccumL (\ (d, env) (n ::: t) -> let v = tintro alg n d in ((succ d, env :> v), im (Just v ::: go env t))) (level, env) ts
      in fn alg ts' (go env' b')
    f S.:$$ a ->
      let (f', a') = splitl (S.unTApp . snd) (s, f S.:$$ a)
      in app alg (go env f') (fmap (ex . go env) a')
    a S.:-> b -> fn alg [ex (Nothing ::: go env a)] (go env b)
    l S.:** r -> prd alg [go env l, go env r]
    where
    level = Level (length env)

foldSExpr :: Algebra p -> Stack p -> Spanned (S.Expr a) -> p
foldSExpr alg = go
  where
  go env (s, e) = case e of
    S.Free  n -> var alg (Global Nothing n)
    S.Bound n -> env ! getIndex n
    S.Hole  n -> hole alg n
    f S.:$  a ->
      let (f', a') = splitl (S.unApp . snd) (s, f S.:$ a)
      in app alg (go env f') (fmap (ex . go env) a')
    l S.:*  r -> prd alg [go env l, go env r]
    S.Comp c  -> case snd c of
      S.Expr e     -> lam alg [ go env e ]
      S.Clauses cs -> lam alg (map (uncurry (cls env)) cs)

  cls env ps b = let ((_, env'), ps') = mapAccumL (\ (d, env) -> fmap (ex . (::: Nothing)) . pat d env) (Level (length env), env) ps in clause alg (toList ps') (go env' b)

  pat d env (_, p) = case p of
    S.Wildcard -> ((d, env), wildcard alg)
    S.Var n    -> let v = intro alg n d in ((succ d, env:>v), v)
    S.Con n ps ->
      let ((d', env'), ps') = subpatterns d env ps
      in ((d', env'), pcon alg (var alg (Cons n)) (fromList ps'))
    S.Tuple ps ->
      let ((d', env'), ps') = subpatterns d env ps
      in ((d', env'), tuple alg ps')
  subpatterns d env ps = mapAccumL (\ (d', env') p -> pat d' env' p) (d, env) ps

foldSCons :: Algebra p -> Stack p -> Spanned (CName ::: Spanned (S.Type a)) -> p
foldSCons alg env = decl alg . bimap (var alg . Cons) (foldSType alg env) . snd

foldSDecl :: Algebra p -> Spanned (S.Decl a) -> p
foldSDecl alg = go Nil
  where
  go env (s, d) = case d of
    t S.:=   b -> defn alg $ foldSType alg env t :=: case b of
      S.DExpr e -> foldSExpr alg env e
      S.DType t -> foldSType alg env t
      S.DData c -> data' alg $ map (foldSCons alg env) c
    t S.:==> b ->
      let (ts, b') = splitr (S.unDForAll . snd) (s, t S.:==> b)
          ((_, env'), ts') = mapAccumL (\ (d, env) (n ::: t) -> let v = var alg (Local n d) in ((succ d, env :> v), im (Just v ::: foldSType alg env t))) (level, env) ts
      in fn alg ts' (go env' b')
    t S.:--> b ->
      let (ts, b') = splitr (S.unDArrow . snd) (s, t S.:--> b)
          ((_, env'), ts') = mapAccumL (\ (d, env) (n ::: t) -> let v = var alg (Local n d) in ((succ d, env :> v), ex (Just v ::: foldSType alg env t))) (level, env) ts
      in fn alg ts' (go env' b')
    where
    level = Level (length env)

foldSModule :: Algebra p -> Spanned (S.Module a) -> p
foldSModule alg (_, S.Module m ds) = module_ alg $ m ::: Just (var alg (Global (Just (MName (T.pack "Kernel"))) (T (TName (UName (T.pack "Module")))))) :=: map (\ (_, (n, d)) -> decl alg (var alg (Global (Just m) n) ::: foldSDecl alg d)) ds
