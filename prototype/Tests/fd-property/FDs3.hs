
--  SHOULD FAIL (Violates FD)

class forall (a :: *) (b :: *) (c :: *). C a b c | a -> b where
  foo :: a -> c -> b

class forall (a :: *) (b :: *). D1 a b | a -> b where
  bar :: a -> b

class forall (a :: *) (b :: *). D2 a b | a -> b where
  baz :: a -> b

data Nat  = Zero | Succ Nat
data Bool = True | False
data List (a :: *) = Nil | Cons a (List a)

-- undefined = let x = x in x

instance forall (a :: *) (b :: *). D1 a b => C (List a) (List b) Nat where
  foo = \xs. \n. case xs of
                   Cons y ys -> Cons (bar y) Nil

instance forall (a :: *) (b :: *). D2 a b => C (List a) (List b) Bool where
  foo = \xs. \n. case xs of
                   Cons y ys -> Cons (baz y) Nil

