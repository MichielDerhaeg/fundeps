
data List (a :: *) = Nil | Cons a (List a)

class forall (a :: *) (b :: *). C1 a b | a -> b where
  c1op :: a -> a

class forall (a :: *) (b :: *). C2 a b | a -> b where
  c2op :: a -> a

class forall (a :: *) (b :: *). C a b | a -> b where
  cop :: a -> a

-- undefined :: forall a. a
undefined = let x = x in x

instance forall (a :: *) (b :: *). (C1 a b, C2 a b) => C a b where
  cop = undefined

-- SHOULD FAIL due to Ambiguous Witness Derivation
-- CURRENTLY SUCCEEDS THOUGH!
\x. x

