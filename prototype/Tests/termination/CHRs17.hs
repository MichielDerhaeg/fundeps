
-- THIS EXAMPLE VIOLATES THE BOUND VARIABLE CONDITION BUT ACCORDING TO OUR SPEC
-- IT SHOULD WORK I BELIEVE (THE VARIABLES ARE INDIRECTLY DETERMINED).

class forall (a :: *). D a where
  d :: a -> a

class forall (a :: *) (b :: *). F a b | a -> b where
  f :: a -> b

data List (a :: *) = Nil | Cons a (List a)
undefined = let x = x in x

instance forall (a :: *). F (List a) (List (List a)) where
  f = undefined

instance forall (a :: *) (c :: *). (D c, F a c) => D (List a) where
  d = undefined

-- IT DOES SEEM TO COMPILE AND TERMINATE PROPERLY NOW. :-)
\x. x

