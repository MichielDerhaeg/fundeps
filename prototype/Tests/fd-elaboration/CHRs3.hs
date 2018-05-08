
class forall (a :: *) (b :: *) (c :: *). Mul a b c | a b -> c where
  mul :: a -> b -> c

data List (a :: *) = Nil | Cons a (List a)

undefined = let x = x in x

instance forall (a :: *) (b :: *) (c :: *).
           Mul a b c => Mul a (List b) (List c) where
  mul = undefined

-- SHOULD COMPILE and generate:
-- axiom g (a, b) : FD a [b] ~ [FD a b]

\x. x

