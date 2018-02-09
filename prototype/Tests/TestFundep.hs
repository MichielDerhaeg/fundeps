class forall (a :: *) (b :: *). A a b | a -> b where
  fa :: a -> b

class forall (a :: *) (b :: *). A a b => B a where
  someMethod :: a -> a

someMethod
