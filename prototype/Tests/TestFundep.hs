class SomeClass (a :: *) (b :: *) (c :: *) | a -> b, a b -> c,c -> a b where
  someMethod :: a -> c

someMethod
