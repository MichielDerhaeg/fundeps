
data Nat = Zero | Succ Nat
data List (a :: *) = Nil | Cons a (List a)
data Tup (a :: *) (b :: *) = MkTup a b

class forall (a :: *) (b :: *). G a b | a -> b where
  gop :: a -> a

class forall (a :: *) (b :: *). H a b | a -> b where
  hop :: a -> a

class forall (a :: *) (b :: *). F a b | a -> b where
  fop :: a -> a

-- undefined :: forall a. a
undefined = let x = x in x

instance forall (a :: *) (b :: *) (c :: *). (G a (Tup a Nat), H c b) => F (List a) (List b) where
  fop = undefined

-- SHOULD SUCCEED

-- CURRENTLY FAILS WITH THIS:
--
-- || Ambigiuous context : bs : [c_uR],
-- ||                      as : [a_uP, b_uQ, c_uR],
-- ||                      class constraints : [G a_uP (Tup a_uP Nat), H c_uR b_uQ]

-- context is actually ambiguous

