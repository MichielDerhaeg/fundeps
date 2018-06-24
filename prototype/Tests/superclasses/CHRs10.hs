
data List (a :: *) = Nil | Cons a (List a)
undefined = let x = x in x

class forall (a :: *) (b :: *). D a b | a -> b where
  d :: a -> b

class forall (a :: *) (b :: *). D a b => C a b where
  c :: a -> b

-- Cool, if we omit this it doesn't work (as it should)
instance forall (a :: *). D (List a) a where
  d = undefined

instance forall (a :: *). C (List a) a where
  c = undefined
-- TODO: We actually need to extend this example, to see whether the equality
-- constraint from the superclass becomes available. We'll talk about it.

