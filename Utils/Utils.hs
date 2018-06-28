{-# LANGUAGE CPP #-}

module Utils.Utils where

import           Control.Monad (unless, when)
import           Data.List     (nub)

#if __GLASGOW_HASKELL__ >= 800
import GHC.Stack (HasCallStack)
#endif

-- | Zip two lists into a list of tuples. Fail if lengths don't match.
#if __GLASGOW_HASKELL__ < 800
zipExact :: [a] -> [b] -> [(a,b)]
#else
zipExact :: HasCallStack => [a] -> [b] -> [(a,b)]
#endif
zipExact = zipWithExact (,)

-- | Zip two lists into a list using a combining function. Fail if lengths don't match.
#if __GLASGOW_HASKELL__ < 800
zipWithExact :: (a -> b -> c) -> [a] -> [b] -> [c]
#else
zipWithExact :: HasCallStack => (a -> b -> c) -> [a] -> [b] -> [c]
#endif
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
