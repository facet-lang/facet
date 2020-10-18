{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
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


foldCValue :: forall p . Algebra p -> Stack p -> C.Value -> p
foldCValue alg = go
  where
  go :: Stack p -> C.Value -> p
  go env = \case
    C.Type  -> _Type alg
    t C.:=> b  ->
      let (vs, (_, b')) = splitr C.unForAll' (d, t C.:=> b)
          binding env (n ::: _T) = (env :> tvar env (n ::: _T), P (pl n) (name (out n) (Level (length env)) ::: go env _T))
          name n d
            | T.null (getUName n) = Nothing
            | otherwise           = Just (tintro alg n d)
          (env', vs') = mapAccumL binding env vs
      in fn alg vs' (go env' b')
    C.Lam n b  ->
      let (vs, (_, b')) = splitr C.unLam' (d, C.Lam n b)
          binding env (n ::: _T) = (env :> lvar env (n ::: _T), P (pl n) (unPl_ (tintro alg) (intro alg) n (Level (length env)) ::: Just (go env _T)))
          (env', vs') = mapAccumL binding env vs
      in lam alg [clause alg vs' (go env' b')]
    -- FIXME: there’s no way of knowing if the quoted variable was a type or expression variable
    -- FIXME: should maybe print the quoted variable differently so it stands out.
    C.Neut h e ->
      let elim h sp  Nil     = case sp Nil of
            Nil -> h
            sp  -> app alg h sp
          elim h sp  (es:>e) = case e of
            C.App a   -> elim h (sp . (:> fmap (go env) a)) es
            C.Case ps -> case' alg (elim h id es) (map clause ps)
          h' = C.unHead (ann' alg . bimap (var alg . qvar) (go env)) ((env !) . getIndex . levelToIndex d) (ann' alg . bimap (var alg . Metavar) (go env)) h
          clause (p, b) =
            let ((env', p'), v) = pat env p
            in (p', go env' (b v))
      in elim h' id e
    C.VCon n p -> app alg (ann' alg (bimap (var alg . qvar) (go env) n)) (fmap (ex . go env) p)
    where
    d = Level (length env)
  tvar env n = ann' alg (var alg (TLocal (out (tm n)) (Level (length env))) ::: go env (ty n))
  lvar env n = ann' alg (var alg (unPl_ TLocal Local (tm n) (Level (length env))) ::: go env (ty n))

  pat env = \case
    C.PVar n    -> let { d = Level (length env) ; v = ann' alg (var alg (Local (tm n) d) ::: go env (ty n)) } in ((env :> v, v), C.PVar (C.free d))
    C.PCon n ps ->
      let ((env', p'), ps') = subpatterns env ps
      in ((env', pcon alg (ann' alg (bimap (var alg . qvar) (go env) n)) p'), C.PCon n ps')
  subpatterns env ps = mapAccumL (\ (env', ps) p -> let ((env'', v), p') = pat env' p in ((env'', ps:>v), p')) (env, Nil) ps

foldCModule :: Algebra p -> C.Module -> p
foldCModule alg (C.Module n ds) = module_ alg
  $   n
  ::: Just (var alg (Global (Just (MName (T.pack "Kernel"))) (T (TName (UName (T.pack "Module"))))))
  :=: map def ds
  where
  def (m :.: n, d ::: t) = decl alg
    $   var alg (Global (Just m) n)
    ::: defn alg (foldCValue alg Nil t
    :=: case d of
      C.DTerm b  -> foldCValue alg Nil b
      C.DType b  -> foldCValue alg Nil b
      C.DData cs -> data' alg
        $ map (decl alg . bimap (var alg . Cons) (foldCValue alg Nil)) cs)


foldSType :: Algebra p -> Stack p -> Spanned S.Type -> p
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
    where
    level = Level (length env)

foldSExpr :: Algebra p -> Stack p -> Spanned S.Expr -> p
foldSExpr alg = go
  where
  go env (s, e) = case e of
    S.Free  n -> var alg (Global Nothing n)
    S.Bound n -> env ! getIndex n
    S.Hole  n -> hole alg n
    f S.:$  a ->
      let (f', a') = splitl (S.unApp . snd) (s, f S.:$ a)
      in app alg (go env f') (fmap (ex . go env) a')
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
  subpatterns d env ps = mapAccumL (\ (d', env') p -> pat d' env' p) (d, env) ps

foldSCons :: Algebra p -> Stack p -> Spanned (CName ::: Spanned S.Type) -> p
foldSCons alg env = decl alg . bimap (var alg . Cons) (foldSType alg env) . snd

foldSDecl :: Algebra p -> Spanned S.Decl -> p
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

foldSModule :: Algebra p -> Spanned S.Module -> p
foldSModule alg (_, S.Module m ds) = module_ alg $ m ::: Just (var alg (Global (Just (MName (T.pack "Kernel"))) (T (TName (UName (T.pack "Module")))))) :=: map (\ (_, (n, d)) -> decl alg (var alg (Global (Just m) n) ::: foldSDecl alg d)) ds
