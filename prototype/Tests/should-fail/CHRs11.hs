
data Nat  = Zero | Succ Nat
data Bool = True | False

class forall (a :: *). C a where
  f :: a -> a

instance C Nat where
  f = \x. x

instance C Bool where
  f = \x. Zero -- This is ill-typed, so the program should fail.

-- SHOULD FAIL. IT DOES, BUT WE GET A "TODO" :P

\x. x

