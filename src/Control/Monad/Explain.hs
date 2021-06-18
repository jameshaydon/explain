{-# LANGUAGE UndecidableInstances #-}

module Control.Monad.Explain where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text

class Explanation e where
  plainly :: e
  paralleled :: [e] -> e
  sequenced :: [e] -> e
  contrasted :: e -> e -> e

instance Explanation Text where
  plainly = ""
  paralleled = Text.intercalate ", "
  sequenced = Text.intercalate "; "
  contrasted x y = x <> ", but: " <> y

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
        ((e, Just f), (e', Just x)) -> (paralleled [e, e'], Just (f x))
        ((e, _), (e', _)) -> (paralleled [e, e'], Nothing)

instance (Explanation e, Applicative f) => Alternative (ExplainT e f) where
  empty = failureT plainly
  ExplainT ax <|> ExplainT ay = ExplainT az
    where
      az = go <$> ax <*> ay
      go x_ y_ = case (x_, y_) of
        ((e, Nothing), (e', Nothing)) -> (paralleled [e, e'], Nothing)
        ((e, Just x), (e', Just _)) -> (paralleled [e, e'], Just x)
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
            pure (sequenced [e, e'], y_)

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
        pure (sequenced [e, e'], z)
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

-- * An explanation type

data Expl cust
  = EPlain
  | EPar [Expl cust]
  | ESeq [Expl cust]
  | EContrast (Expl cust) (Expl cust)
  | ECustom cust
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

customError :: (MonadError (Expl e) m) => e -> m a
customError = throwError . ECustom

instance Explanation (Expl cust) where
  plainly = EPlain
  paralleled = EPar
  sequenced = ESeq
  contrasted = EContrast

{-
instance Pretty cust => Pretty (Expl cust) where
  pretty = \case
    EPlain -> mempty
    EPar es -> bullets (pretty <$> es)
    ESeq es -> bulletItems " " "∴" (pretty <$> es)
    EContrast e e' ->
      vsep
        [ "Have:",
          indent 2 (pretty e),
          "However:",
          indent 2 (pretty e')
        ]
    ECustom cust -> pretty cust
-}

-- | The explanations produced are somewhat redundant, so they are optimised.
--
-- >>> optimizeExpl ECustom (ESeq [EPar [ECustom "a", EPlain, EPar [ECustom "b"], ECustom "a"], ECustom "c"])
-- ESeq [EPar [ECustom "a",ECustom "b"],ECustom "c"]
--
-- TODO(james): the following does a little /too much/ flattening for paralleled
-- explanations. I think the solutions is to have to give the parallel
-- combinator an extra flag argument to indicate if it wants to be flattened or
-- not. Or maybe just have an extra 'Group' combinator.
optimizeExpl :: forall a. (Ord a) => (a -> Expl a) -> Expl a -> Expl a
optimizeExpl optCust = fixPoint (100 :: Int) (dedup . opt)
  where
    opt :: Expl a -> Expl a
    opt e = unwrap $ case e of
      EPlain -> EPlain
      EPar es -> EPar $ seqopt (concatMap flatPar es)
      ESeq es -> ESeq $ seqopt (concatMap flatSeq es)
      EContrast e' e'' -> EContrast (opt e') (opt e'')
      ECustom c -> optCust c
    dedup :: Expl a -> Expl a
    dedup e = evalState (dd e) mempty
    dd :: Expl a -> State (Set (Expl a)) (Expl a)
    dd expl = case expl of
      EPar es -> EPar <$> ddseq es
      ESeq es -> ESeq <$> ddseq es
      EContrast e e' -> EContrast <$> dd e <*> dd e'
      e -> pure e
    ddseq :: [Expl a] -> State (Set (Expl a)) [Expl a]
    ddseq [] = pure []
    ddseq (e : es) = do
      e' <- dd e
      seen <- get
      if Set.member e' seen
        then ddseq es
        else do
          modify (Set.insert e')
          (e' :) <$> ddseq es
    seqopt es = filter keep (opt <$> es)
    keep EPlain = False
    keep (EPar []) = False
    keep (ESeq []) = False
    keep _ = True
    unwrap (ESeq [e]) = e
    unwrap (EPar [e]) = e
    unwrap e = e
    flatPar (EPar es) = concatMap flatPar es
    flatPar e = [e]
    flatSeq (ESeq es) = concatMap flatSeq es
    flatSeq e = [e]

    fixPoint 0 _ x = x
    fixPoint bound f x =
      if x == f x
        then x
        else fixPoint (bound - 1) f (f x)
