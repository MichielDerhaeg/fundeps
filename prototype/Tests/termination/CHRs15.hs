
-- TEST IF WE CHECK PROPERLY THE PATERSON CONDITIONS.
-- THE FOLLOWING PROGRAM DOES NOT SATISFY THE BASIC CONDITIONS BUT IT
-- DOES SATISFY THE PATERSON CONDITIONS, WHICH WE WANT TO ENFORCE.

class forall (a :: *) (b :: *). C a b where
  c :: a -> b

undefined = let x = x in x
data List (a :: *) = Nil | Cons a (List a)
data Tup (a :: *) (b :: *) = MkTup a b

instance forall (a :: *) (b :: *). (C b b, C b (List a)) => C (List a) (Tup b b) where
  c = undefined

-- SHOULD COMPILE. IT SATISFIES THE PATERSON CONDITIONS.
