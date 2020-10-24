module Facet.Algebra
( -- * Algebras
  Var(..)
, Algebra(..)
  -- * Folds
  -- ** Core
, foldCValue
, foldCModule
) where

import           Data.Bifunctor (bimap)
import           Data.Foldable (toList)
import qualified Data.Text as T
import           Data.Traversable (mapAccumL)
import qualified Facet.Core as C
import           Facet.Name
import           Facet.Stack
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
