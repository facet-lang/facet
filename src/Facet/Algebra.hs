{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Algebra
( -- * Folds
  Var(..)
, ExprAlg(..)
, PatternAlg(..)
, foldValue
, foldSType
) where

import           Data.Bifunctor (bimap)
import           Data.Foldable (toList)
import           Data.Text (Text)
import           Data.Traversable (mapAccumL)
import qualified Facet.Core as C
import           Facet.Name
import           Facet.Stack
import qualified Facet.Surface as S
import           Facet.Syntax
import           Text.Parser.Position

data Var
  = Global (Maybe MName) DName
  | Local UName Level
  | Meta Level
  | Cons CName

qvar :: QName -> Var
qvar (m :.: n) = Global (Just m) n

data ExprAlg p = ExprAlg
  { var :: Var -> p
  , intro :: Pl_ UName -> Level -> p
  , lam
    :: [Pl_ (p ::: Maybe p)] -- the bound variables.
    -> p                     -- the body.
    -> p
  , fn
    :: [Pl_ (Maybe p ::: p)] -- the argument types/bindings
    -> p                     -- the return type
    -> p
  , app :: p -> Stack (Pl_ p) -> p
  , prd :: [p] -> p
  , hole :: Text -> p
  , _Type :: p
  , _Void :: p
  , _Unit :: p
  , ann' :: (p ::: p) -> p
  , case' :: p -> [(p, p)] -> p -- ^ will only arise in core
  , pattern :: PatternAlg p
  }

data PatternAlg p = PatternAlg
  { wildcard :: p
  , pcon     :: p -> Stack p -> p
  , tuple    :: [p] -> p
  }


foldValue :: ExprAlg p -> Level -> C.Value p -> p
foldValue alg = go
  where
  go d = \case
    C.Type  -> _Type alg
    C.Void  -> _Void alg
    C.TUnit -> _Unit alg
    C.Unit  -> prd alg []
    t C.:=> b  ->
      let (vs, (d', b')) = splitr (C.unLam' var') (d, t C.:=> b)
      in fn alg (map (\ (d, n ::: _T) -> P (pl n) (Just (intro alg n d) ::: go d _T)) vs) (go d' b')
    C.Lam n b  ->
      let (vs, (d', b')) = splitr (C.unLam' var') (d, C.Lam n b)
      in lam alg (map (\ (d, n) -> P (pl (tm n)) (intro alg (tm n) d ::: Just (go d (ty n)))) vs) (go d' b')
    -- FIXME: there’s no way of knowing if the quoted variable was a type or expression variable
    -- FIXME: should maybe print the quoted variable differently so it stands out.
    C.Neut h e ->
      let elim h Nil Nil     = h
          elim h sp  Nil     = app alg h sp
          elim h sp  (es:>e) = case e of
            C.App a   -> elim h (sp:>fmap (go d) a) es
            C.Case ps -> case' alg (elim h Nil es) (map clause ps)
          h' = C.unHead (ann' alg . bimap (var alg . qvar) (go d)) id (var alg . Local __) (ann' alg . bimap (var alg . Meta) (go d)) h
          clause (p, b) =
            let ((d', p'), v) = pat d p
            in (p', go d' (b v))
      in elim h' Nil e
    C.TPrd l r -> prd alg [go d l, go d r]
    C.Prd  l r -> prd alg [go d l, go d r]
    C.VCon n p -> app alg (ann' alg (bimap (var alg . qvar) (go d) n)) (fmap (ex . go d) p)
  var' d n = ann' alg (var alg (Local (out (tm n)) d) ::: go d (ty n))

  pat d = \case
    C.Wildcard -> ((d, wildcard (pattern alg)), C.Wildcard)
    C.Var n    -> let v = ann' alg (var alg (Local (tm n) d) ::: foldValue alg d (ty n)) in ((succ d, v), C.Var (C.free v))
    C.Con n ps ->
      let ((d', p'), ps') = subpatterns d ps
      in ((d', pcon (pattern alg) (ann' alg (bimap (var alg . qvar) (foldValue alg d) n)) p'), C.Con n ps')
    C.Tuple ps ->
      let ((d', p'), ps') = subpatterns d ps
      in ((d', tuple (pattern alg) (toList p')), C.Tuple ps')
  subpatterns d ps = mapAccumL (\ (d', ps) p -> let ((d'', v), p') = pat d' p in ((d'', ps:>v), p')) (d, Nil) ps


foldSType :: ExprAlg p -> Stack p -> Spanned (S.Type a) -> p
foldSType alg = go
  where
  go env (s, t) = case t of
    S.TFree n  -> var alg (Global Nothing n)
    S.TBound n -> env ! getIndex n
    S.THole n  -> hole alg n
    S.Type     -> _Type alg
    S.Void     -> _Void alg
    S.TUnit    -> _Unit alg
    t S.:=> b ->
      let (ts, b') = splitr (S.unForAll . snd) (s, t S.:=> b)
          ((_, env'), ts') = mapAccumL (\ (d, env) (n ::: t) -> let v = var alg (Local n d) in ((succ d, env :> v), im (Just v ::: go env t))) (level, env) ts
      in fn alg ts' (go env' b')
    f S.:$$ a ->
      let (f', a') = splitl (S.unTApp . snd) f
      in app alg (go env f') (fmap (ex . go env) (a' :> a))
    a S.:-> b -> fn alg [ex (Nothing ::: go env a)] (go env b)
    l S.:** r -> prd alg [go env l, go env r]
    where
    level = Level (length env)
