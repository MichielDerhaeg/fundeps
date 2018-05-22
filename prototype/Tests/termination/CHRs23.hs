

class forall (a :: *) (b :: *) (c :: *). F a b c | a -> b where
  fop :: a -> b -> c

class forall (a :: *) (b :: *). H a b | a -> b where
  hop :: a -> b

undefined = let x = x in x
data List (a :: *) = Nil | Cons a (List a)
data Bool = True | False
data Char = MkChar -- Placeholder

instance forall (a :: *) (b :: *). F a b Bool => F (List a) (List b) Bool where
  fop = undefined

instance forall (a :: *) (b :: *). H a b => F (List a) (List b) Char where
  fop = undefined

-- this clearly violates compatability/consistency

\x. x

