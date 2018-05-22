
data List (a :: *) = Nil | Cons a (List a)

class forall (a :: *) (b :: *). G a b | a -> b where
  gop :: a -> a

class forall (a :: *) (b :: *). H a b | a -> b where
  hop :: a -> a

class forall (a :: *) (b :: *). F a b | a -> b where
  fop :: a -> a

-- undefined :: forall a. a
undefined = let x = x in x

instance forall (a :: *) (b :: *) (c :: *). (G a c, H c b) => F (List a) (List b) where
  fop = undefined

-- SHOULD SUCCEED

-- CURRENTLY FAILS WITH THIS:
--
-- || Ambigiuous context : bs : [c_uI],
-- ||                      as : [a_uJ, b_uK, c_uI],
-- ||                      class constraints : [G a_uJ c_uI, H c_uI b_uK]

-- instance fails termination conditions, 'c' appears more often in context
-- than in the head, GHC agrees with me :p

\x. x

