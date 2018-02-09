class forall (a :: *) (b :: *). A a b | a -> b where
  fa :: a -> b

class forall (a :: *) (b :: *). A a b => B a where
  fb :: a -> a

class forall (a :: *) (b :: *). G a b | a -> b where
  fg :: a -> b

class forall (a :: *) (b :: *). H a b | a -> b where
  fh :: a -> b

class forall (a :: *) (b :: *). F a b | a -> b where
  ff :: a -> b

instance forall (a::*) (b::*) (c::*). (G a c, H c b) => F a b where
  ff = \x. x

fa
