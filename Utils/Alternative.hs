module Utils.Alternative where

import           Control.Applicative
import           Control.Arrow       (second)
import           Data.Monoid         ((<>))

exhaust :: (Alternative m, Monad m) => (a -> m [a]) -> [a] -> m [a]
exhaust f xs = do
  (output, rest) <- tryRule f xs
  let new_xs = output <> rest
  exhaust f new_xs <|> pure new_xs

tryRule :: Alternative f => (a -> f b) -> [a] -> f (b, [a])
tryRule _f []     =  empty
tryRule f (x:xs)  =  flip (,) xs  <$>         f x
                 <|> second (x :) <$> tryRule f xs

doAlt2 :: Alternative f => (a -> b -> c) -> (a -> f a) -> a -> (b -> f b) -> b -> f c
doAlt2 pat f1 x1 f2 x2 =  pat <$>   f1 x1 <*> pure x2
                      <|> pat <$> pure x1 <*>   f2 x2

doAlt3 ::
     Alternative f
  => (a -> b -> c -> d)
  -> (a -> f a)
  -> a
  -> (b -> f b)
  -> b
  -> (c -> f c)
  -> c
  -> f d
doAlt3 pat f1 x1 f2 x2 f3 x3 =  pat <$>   f1 x1 <*> pure x2 <*> pure x3
                            <|> pat <$> pure x1 <*>   f2 x2 <*> pure x3
                            <|> pat <$> pure x1 <*> pure x2 <*>   f3 x3

doAltList :: Alternative f => (a -> f a) -> [a] -> f [a]
doAltList _f []     = empty
doAltList  f (x:xs) = doAlt2 (:) f x (doAltList f) xs

keep :: (Alternative m, Monad m) => (a -> m a) -> a -> m a
keep f x = do
  x' <- f x
  keep f x' <|> pure x'
