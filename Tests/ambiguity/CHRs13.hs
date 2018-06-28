
class forall (a :: *) (b :: *). C a b | a -> b where
  c :: a -> a

-- with signature
g1 :: forall (a :: *). forall (b :: *). C a b => a -> a
   = c

-- without signature
g2 = c

-- SHOULD PASS. 'b' IS DETERMINED

