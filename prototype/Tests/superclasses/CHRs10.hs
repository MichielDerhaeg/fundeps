
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

data Int = MkInt
data Bool = True | False

instance D Int Bool where
  d = \x. True

instance C Int Bool where
  c = \x. True

f :: forall (b :: *). C Int b => b -> Bool
  = \x. x

f2 :: forall (e :: *). forall (c1 :: *). forall (c2 :: *). C c2 c1 => C c1 e => c2 -> e
   = \x. c (c x)
