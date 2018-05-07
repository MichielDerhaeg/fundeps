
data Bool = True | False
data Nat = Zero | Succ Nat

class forall (a :: *) (b :: *). C a b | a -> b where
  foo :: a -> b

instance C Bool Nat where
  foo = \b. Zero

-- Full signature: C a b => a -> b
bar1 :: forall (a :: *). forall (b :: *). C a b => a -> b
     = foo

-- Substitute [a |-> Bool]
bar2 :: forall (b :: *). C Bool b => Bool -> b
     = foo

-- Substitute [a |-> Bool, b |-> Nat]
bar3 :: Bool -> Nat
     = foo

-- SHOULD PASS (and it seems to do so :-))
\x. x

