
class forall (a :: *) (b :: *). T a b | a -> b where
  top :: a -> b

undefined = let x = x in x
data Nat  = Zero | Succ Nat

instance T Nat Nat where
  top = undefined

class forall (a :: *). C a where
  cop :: forall (b :: *). T a b => a -> b

instance C Nat where
  cop = \x. Succ x

-- Translation of an associated-type-family-example
-- to a functional-dependencies-based one.
\x. x

