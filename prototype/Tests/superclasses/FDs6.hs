
class forall (a :: *) (b :: *). C a b | a -> b where
  fc :: a -> a

class forall (a :: *) (b :: *). C a b => D a where
  fd :: a -> a

\x. x

--  SHOULD SUCCEED (Existentials in the superclasses are allowed if they are determined)

