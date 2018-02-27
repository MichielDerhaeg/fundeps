
module Utils.Utils where

import Data.List (nub)
import Control.Monad (unless, when)

-- | Zip two lists into a list of tuples. Fail if lengths don't match.
zipExact :: [a] -> [b] -> [(a,b)]
zipExact = zipWithExact (,)

-- | Zip two lists into a list using a combining function. Fail if lengths don't match.
zipWithExact :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWithExact _f []     []     = []
zipWithExact  f (x:xs) (y:ys) = f x y : zipWithExact f xs ys
zipWithExact _f _      _      = error "zipWithExact: length mismatch"

-- TODO doc all
zipWithExactM :: (Monad m) => (a -> b -> m c) -> [a] -> [b] -> m [c]
zipWithExactM f l1 l2 = sequence $ zipWithExact f l1 l2

distinct :: Eq a => [a] -> Bool
distinct xs = nub xs == xs

unlessM :: Monad m => m Bool -> m () -> m ()
unlessM condition f = condition >>= (`unless` f)

whenM :: Monad m => m Bool -> m () -> m ()
whenM condition f = condition >>= (`when` f)

findJust :: [Maybe a] -> Maybe a
findJust (Just x:_) = Just x
findJust (Nothing:xs) = findJust xs
findJust [] = Nothing
