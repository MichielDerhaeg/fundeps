
--  SHOULD FAIL (Violates FD)

data List (a :: *) = Nil | Cons a (List a)

class forall (a :: *) (b :: *). C a b | a -> b where
  cop :: a -> a

-- undefined :: forall a. a
undefined = let x = x in x

instance forall (a :: *) (b :: *). C a b => C (List a) (List b) where
  cop = undefined

-- SHOULD COMPILE
--
-- Should create the following witness constraint scheme:
-- axiom g (t) : FC(List t) ~ List (FC(t))
\x. x

