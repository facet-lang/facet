module Facet.Algebra
( -- * Algebras
  Var(..)
, Algebra(..)
  -- * Folds
  -- ** Core
, foldCValue
, foldCModule
  -- ** Surface
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


-- * Folds

-- ** Core

foldCValue :: Algebra p -> Stack p -> C.Value -> p
foldCValue alg = go
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

foldCModule :: Algebra p -> C.Module -> p
foldCModule alg (C.Module mname is ds) = module_ alg
  $   mname
  ::: Just (var alg (Global (Just (MName (T.pack "Kernel"))) (T (UName (T.pack "Module")))))
  :=: (map (\ (C.Import n) -> import' alg n) is, map def ds)
  where
  def (n, Nothing ::: t) = decl alg
    $   var alg (Global (Just mname) n)
    ::: foldCValue alg Nil t
  def (n, Just d  ::: t) = decl alg
    $   var alg (Global (Just mname) n)
    ::: defn alg (foldCValue alg Nil t
    :=: case d of
      C.DTerm b  -> foldCValue alg Nil b
      C.DData cs -> data' alg
        $ map (\ (n :=: _ ::: _T) -> decl alg (var alg (Cons n) ::: foldCValue alg Nil _T)) cs)


-- ** Surface

foldSExpr :: Algebra p -> Stack p -> S.Ann S.Expr -> p
foldSExpr alg = go
  where
  go env (S.Ann s e) = case e of
    S.Var (S.Free m n) -> var alg (Global m n)
    S.Var (S.Bound n) -> env ! getIndex n
    S.Hole  n -> hole alg n
    S.Type     -> _Type alg
    S.Interface -> _Interface alg
    S.ForAll t b ->
      let (ts, b') = splitr (S.unForAll . S.out) (S.Ann s (S.ForAll t b))
          -- FIXME: fold the signature
          binding (d, env) (S.Binding p n _ t)
            | T.null (getUName n) = ((d, env), P p ([] ::: go env t))
            | otherwise           = let v = tintro alg n d in ((succ d, env :> v), P p ([v] ::: go env t))
          ((_, env'), ts') = mapAccumL binding (Level (length env), env) ts
      in fn alg ts' (go env' b')
    S.App f a ->
      let (f', a') = splitl (S.unApp . S.out) (S.Ann s (S.App f a))
      in app alg (go env f') (fmap (ex . go env) a')
    S.Comp (S.Ann _ c)  -> case c of
      S.Expr e     -> lam alg [ go env e ]
      S.Clauses cs -> lam alg (map (uncurry (cls env)) cs)

  cls env ps b = let ((_, env'), ps') = mapAccumL (\ (d, env) -> fmap (ex . (::: Nothing)) . pat d env) (Level (length env), env) ps in clause alg (toList ps') (go env' b)

  pat d env (S.Ann _ p) = case p of
    S.PVar n    -> let v = intro alg n d in ((succ d, env:>v), v)
    S.PCon n ps ->
      let ((d', env'), ps') = subpatterns d env ps
      in ((d', env'), pcon alg (var alg (Cons n)) ps')
    S.PEff n ps k ->
      let ((d', env'), ps') = subpatterns d env ps
          k' = intro alg k d
      in ((succ d', env' :> k'), peff alg (var alg (Cons n)) ps' k')
  subpatterns d env ps = mapAccumL (\ (d', env') p -> pat d' env' p) (d, env) ps

foldSCons :: Algebra p -> Stack p -> S.Ann (UName ::: S.Ann S.Expr) -> p
foldSCons alg env = decl alg . bimap (var alg . Cons) (foldSExpr alg env) . S.out

foldSDecl :: Algebra p -> S.Ann S.Decl -> p
foldSDecl alg (S.Ann _ d) = case d of
  S.DDecl d -> foldSDDecl alg d
  S.TDecl t -> foldSTDecl alg t

foldSDDecl :: Algebra p -> S.Ann S.DDecl -> p
foldSDDecl alg = go Nil
  where
  go env (S.Ann s d) = case d of
    S.DDBody t b -> defn alg $ foldSExpr alg env t :=: data' alg (map (foldSCons alg env) b)
    S.DDForAll t b ->
      let (ts, b') = splitr (S.unDDForAll . S.out) (S.Ann s (S.DDForAll t b))
          -- FIXME: fold the signature
          ((_, env'), ts') = mapAccumL (\ (d, env) (S.Binding p n _ t) -> let v = var alg (Local n d) in ((succ d, env :> v), P p ([v] ::: foldSExpr alg env t))) (level, env) ts
      in fn alg ts' (go env' b')
    where
    level = Level (length env)

foldSTDecl :: Algebra p -> S.Ann S.TDecl -> p
foldSTDecl alg = go Nil
  where
  go env (S.Ann s d) = case d of
    S.TDBody t b -> defn alg $ foldSExpr alg env t :=: foldSExpr alg env b
    S.TDForAll t b ->
      let (ts, b') = splitr (S.unTDForAll . S.out) (S.Ann s (S.TDForAll t b))
          -- FIXME: fold the signature
          ((_, env'), ts') = mapAccumL (\ (d, env) (S.Binding p n _ t) -> let v = var alg (Local n d) in ((succ d, env :> v), P p ([v] ::: foldSExpr alg env t))) (level, env) ts
      in fn alg ts' (go env' b')
    where
    level = Level (length env)

foldSModule :: Algebra p -> S.Ann S.Module -> p
foldSModule alg (S.Ann _ (S.Module m is ds)) = module_ alg $ m ::: Just (var alg (Global (Just (MName (T.pack "Kernel"))) (T (UName (T.pack "Module"))))) :=: (map (\ (S.Ann _ (S.Import n)) -> import' alg n) is, map (\ (S.Ann _ (n, d)) -> decl alg (var alg (Global (Just m) n) ::: foldSDecl alg d)) ds)
