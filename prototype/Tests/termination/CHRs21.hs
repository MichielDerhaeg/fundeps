
class forall (a :: *) (b :: *). G a b | a -> b where
  gop :: a -> b

class forall (a :: *) (b :: *). H a b | a -> b where
  hop :: a -> b

class forall (a :: *) (b :: *). F a b | a -> b where
  fop :: a -> b

undefined = let x = x in x
data List (a :: *) = Nil | Cons a (List a)

instance forall (a :: *) (b :: *) (c :: *).
           (G a c, H c b) => F (List a) (List b) where
  fop = undefined

-- THIS EXAMPLE REALLY NEEDS THE REFINED WEAK COVERAGE
-- CONDITION (LIBERAGE COVERAGE CONDITION) TO TYPE-CHECK
--
-- fails termination conditions?

\x. x

