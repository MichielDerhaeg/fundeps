data Bool = True | False

data List (a :: *) = Cons a (List a) | Nil

data Nat = Succ Nat | Zero

data Maybe (a:: *) = Just a | Nothing

data Either (a :: *) (b :: *) = Left a | Right b

class forall (a :: *). Eq a where
  eq :: a -> a -> Bool


class forall (a :: *). Eq a => Ord a where
  lessOrEqualThan :: a -> a -> Bool


class forall (f :: * -> *). Functor f where
  fmap :: forall (a :: *). forall (b :: *). (a -> b) -> f a -> f b


instance Eq Bool where
  eq = \a. \b. case a of
                   True  -> case b of
                                True  -> True
                                False -> False
                   False -> case b of
                                True  -> False
                                False -> True

instance Eq Nat where
  eq = \a. \b. case a of
                   Zero  -> case b of
                                Zero  -> True
                                Succ b' -> False
                   Succ a' -> case b of
                                  Zero  -> False
                                  Succ b' -> eq a' b'

instance Ord Nat where
  lessOrEqualThan =
    \a. \b. case a of
                   Zero -> case b of
                                Zero  -> True
                                Succ b' -> True
                   Succ a' -> case b of
                                Zero  -> False
                                Succ b' -> lessOrEqualThan a' b'

instance forall (a :: *). Eq a => Eq (List a) where
  eq =
    \a. \b. case a of
              Nil -> case b of
                       Nil -> True
                       Cons qsdf asdf -> False
              Cons a' as -> case b of
                              Nil -> False
                              Cons b' bs -> case eq a' b' of
                                              False -> False
                                              True -> eq as bs

instance Functor List where
  fmap =
    \f. \l. case l of
              Nil -> Nil
              Cons x xs -> Cons (f x) (fmap f xs)

test :: List Bool -> List (Maybe Bool)
     = \l. fmap Just l

map :: forall (a :: *). forall (b :: *). (a -> b) -> List a -> List b
    = \f. \l. case l of
      Nil -> Nil
      Cons x xs -> Cons (f x) (map f xs)

let id = \x. x in
  \a. \b . eq (fmap id a) b
