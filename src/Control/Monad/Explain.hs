{-# LANGUAGE UndecidableInstances #-}

module Control.Monad.Explain where

import Control.Applicative
import Control.Lens
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import Prettyprinter

class Explanation e where
  plainly :: e
  paralleled :: e -> e -> e
  sequenced :: e -> e -> e

class Dualistic e where
  negated :: e -> e

instance Explanation Text where
  plainly = ""
  paralleled x y = x <> ", " <> y
  sequenced x y = x <> "; " <> y

instance Dualistic Text where
  negated = ("not: " <>)

-- | A monad transformer that adds explanations to other monads. A computation
-- may either fail with an explanation of what went wrong, or succeed with an
-- explanation of what went right.
--
-- @ExplainT@ constructs a monad parameterized over three things:
--
-- * e - The explanation type.
--
-- * m - The inner monad.
--
-- The 'pure' function yields a computation that produces the given value with
-- no explanation, while @>>=@ sequences two subcomputations while accumulating
-- explanations, exiting on the first failure.
--
-- The 'Applicative' and 'Alternative' instances provide explanations for all
-- successesful branches when the computation is successful, and otherwise will
-- privide explanations for all failures.
newtype ExplainT e m a = ExplainT {runExplainT :: m (e, Maybe a)}
  deriving stock (Functor)

mapExplainT :: (m (e, Maybe a) -> n (e, Maybe b)) -> ExplainT e m a -> ExplainT e n b
mapExplainT f m = ExplainT (f (runExplainT m))
{-# INLINE mapExplainT #-}

mapExplanationT :: (Functor f) => (e -> e') -> ExplainT e f a -> ExplainT e' f a
mapExplanationT f (ExplainT fx) = ExplainT (fmap (first f) fx)

successT :: (Applicative f) => e -> a -> ExplainT e f a
successT e x = ExplainT (pure (e, Just x))
{-# INLINE successT #-}

failureT :: (Applicative f) => e -> ExplainT e f a
failureT e = ExplainT (pure (e, Nothing))
{-# INLINE failureT #-}

withExplanationT :: (Monad m) => ExplainT e m a -> ((e, Maybe a) -> ExplainT e m b) -> ExplainT e m b
withExplanationT (ExplainT fx) w = ExplainT $ fx >>= runExplainT . w

instance (Explanation e, Applicative f) => Applicative (ExplainT e f) where
  pure = successT plainly
  ExplainT af <*> ExplainT ax = ExplainT ay
    where
      ay = go <$> af <*> ax
      go f_ x_ = case (f_, x_) of
        ((e, Just f), (e', Just x)) -> (paralleled e e', Just (f x))
        ((_, Just _), (e', Nothing)) -> (e', Nothing)
        ((e, Nothing), (_, Just _)) -> (e, Nothing)
        ((e, _), (e', _)) -> (paralleled e e', Nothing)

instance (Explanation e, Applicative f) => Alternative (ExplainT e f) where
  empty = failureT plainly
  ExplainT ax <|> ExplainT ay = ExplainT az
    where
      az = go <$> ax <*> ay
      go x_ y_ = case (x_, y_) of
        ((e, Nothing), (e', Nothing)) -> (paralleled e e', Nothing)
        ((e, Just x), (e', Just _)) -> (paralleled e e', Just x)
        ((e, Just x), _) -> (e, Just x)
        (_, (e, Just y)) -> (e, Just y)

instance (Explanation e, Monad m) => Monad (ExplainT e m) where
  ExplainT mx >>= f = ExplainT my
    where
      my = do
        (e, x_) <- mx
        case x_ of
          Nothing -> pure (e, Nothing)
          Just x -> do
            (e', y_) <- runExplainT (f x)
            pure (sequenced e e', y_)

instance (Explanation e) => MonadTrans (ExplainT e) where
  lift = ExplainT . fmap ((plainly,) . Just)
  {-# INLINE lift #-}

instance (Explanation e, MonadIO m) => MonadIO (ExplainT e m) where
  liftIO = lift . liftIO
  {-# INLINE liftIO #-}

instance (Explanation e, MonadReader read m) => MonadReader read (ExplainT e m) where
  ask = lift ask
  local = mapExplainT . local
  reader = lift . reader

instance (Explanation e, MonadState s m) => MonadState s (ExplainT e m) where
  get = lift get
  put = lift . put

instance (Monad m, Explanation e) => MonadError e (ExplainT e m) where
  throwError = failureT
  catchError x f = ExplainT $ do
    y <- runExplainT x
    case y of
      (e, Nothing) -> do
        (e', z) <- runExplainT (f e)
        pure (sequenced e e', z)
      z -> pure z

-- * MonadExplain

class (Monad m) => MonadExplain e m | m -> e where
  success :: e -> a -> m a
  failure :: e -> m a
  explain :: e -> Maybe a -> m a
  withExplanation :: m a -> ((e, Maybe a) -> m b) -> m b
  mapExplanation :: (e -> e) -> m a -> m a
  mapExplanation f mx = withExplanation mx (\(e, x_) -> explain (f e) x_)
  success e x = explain e (Just x)
  failure e = explain e Nothing
  {-# MINIMAL explain, withExplanation, mapExplanation #-}

instance (Monad m, Explanation e) => MonadExplain e (ExplainT e m) where
  success = successT
  failure = failureT
  explain e x_ = ExplainT (pure (e, x_))
  withExplanation = withExplanationT
  mapExplanation = mapExplanationT

instance MonadExplain e m => MonadExplain e (ReaderT r m) where
  success e x = lift (success e x)
  failure = lift . failure
  explain e x_ = lift (explain e x_)
  withExplanation x w = ReaderT $ \r ->
    withExplanation (runReaderT x r) (\stuff -> runReaderT (w stuff) r)
  mapExplanation f x = ReaderT $ \r -> mapExplanation f (runReaderT x r)

enot :: (MonadExplain e m) => m a -> m ()
enot x = withExplanation x $ \(e, res) -> case res of
  Nothing -> success e ()
  Just _ -> failure e

guarded :: (Dualistic e, MonadExplain e m) => Bool -> e -> a -> m a
guarded cond e tt  =
  if cond
  then success e tt
  else failure (negated e)

-- * An explanation type

data Dual e = Pos e | Neg e
  deriving stock (Eq, Ord, Show)

instance Dualistic (Dual e) where
  negated (Pos e) = Neg e
  negated (Neg e) = Pos e

data Expl cust
  = EPlain
  | EPar [Expl cust]
  | ESeq [Expl cust]
  | ENeg (Expl cust)
  | Custom cust
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

customError :: (MonadError (Expl e) m) => e -> m a
customError = throwError . Custom

instance Dualistic (Expl e) where
  negated = ENeg

instance Explanation (Expl cust) where
  plainly = EPlain
  paralleled x y = EPar [x, y]
  sequenced x y = ESeq [x, y]

instance Plated (Expl cust) where
  plate :: Traversal' (Expl cust) (Expl cust)
  plate f = \case
    EPar es -> EPar <$> traverse f es
    ESeq es -> ESeq <$> traverse f es
    ENeg e -> ENeg <$> f e
    e -> pure e

instance Pretty cust => Pretty (Expl cust) where
  pretty = \case
    EPlain -> mempty
    EPar es -> bullets (pretty <$> es)
    ESeq es -> bulletItems " " "∴" (pretty <$> es)
    ENeg e -> "Not" <> colon <+> pretty e
    Custom cust -> pretty cust

bullets :: [Doc ann] -> Doc ann
bullets = bulletItems "•" "•"

bulletItems :: Text -> Text -> [Doc ann] -> Doc ann
bulletItems _ _ [] = mempty
bulletItems _ _ [x] = x
bulletItems firstBullet bullet (f : xs) =
  align (vsep (bulletItem firstBullet f : (bulletItem bullet <$> xs)))
  where
    bulletItem b x = pretty b <+> align x

-- | The explanations produced are somewhat redundant, so they are optimised.
--
-- >>> optimizeExpl (ESeq [EPar [ECustom "a", EPlain, EPar [ECustom "b"], ECustom "a"], ECustom "c"])
-- ESeq [EPar [ECustom "a",ECustom "b"],ECustom "c"]
--
-- TODO(james): the following does a little /too much/ flattening for paralleled
-- explanations. I think the solutions is to have to give the parallel
-- combinator an extra flag argument to indicate if it wants to be flattened or
-- not. Or maybe just have an extra 'Group' combinator.
optimizeExpl :: (Dualistic a, Ord a) => Expl a -> Expl a
optimizeExpl = optimizeExplWith Custom

optimizeExplWith :: forall a. (Dualistic a, Ord a) => (a -> Expl a) -> Expl a -> Expl a
optimizeExplWith f = fixPoint 100 (deduplicate . optimize)
  where
    -- [1] Full-tree, bottom-up transformations using functions in [2]
    optimize, deduplicate :: Expl a -> Expl a
    optimize = transform (custom f . squash . shrink)
    deduplicate e = evalState (transformM dedup e) mempty
    -- [2] Simple, non-recursive functions targeting a single node in the tree
    dedup :: Expl a -> State (Set (Expl a)) (Expl a)
    dedup e = do
      seen <- get
      if Set.member e seen
        then pure EPlain
        else modify (Set.insert e) >> pure e
    custom :: (a -> Expl a) -> Expl a -> Expl a
    custom optCust = \case
      Custom c -> optCust c
      e -> e
    squash :: Expl a -> Expl a
    squash = \case
      EPar es -> EPar $ concatMap (\case EPar es' -> es'; e -> [e]) es
      ESeq es -> ESeq $ concatMap (\case ESeq es' -> es'; e -> [e]) es
      ENeg (ENeg e) -> e
      ENeg (EPar es) -> EPar (ENeg <$> es)
      ENeg (Custom e) -> Custom (negated e)
      e -> e
    shrink :: Expl a -> Expl a
    shrink = \case
      EPar [] -> EPlain
      ESeq [] -> EPlain
      EPar [e] -> e
      ESeq [e] -> e
      EPar es -> EPar $ filter hasInner es
      ESeq es -> ESeq $ filter hasInner es
      e -> e
      where
        hasInner = \case
          EPlain -> False
          EPar [] -> False
          ESeq [] -> False
          _ -> True

fixPoint :: (Eq a) => Int -> (a -> a) -> (a -> a)
fixPoint 0 _ x = x
fixPoint bound f x =
  if x == f x
    then x
    else fixPoint (bound - 1) f (f x)
