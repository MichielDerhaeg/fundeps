
class forall (a :: *) (b :: *). G a b | a -> b where
  gop :: a -> b

class forall (a :: *) (b :: *) (c :: *). G a b => F a b c where
  fop :: a -> b -> c

undefined = let x = x in x
data List (a :: *) = Nil | Cons a (List a)
data Nat  = Zero | Succ Nat
data Bool = True | False
data Char = MkChar -- Placeholder

instance G Nat Bool where
  gop = undefined

instance F Nat Bool Char where
  fop = undefined

instance forall (a :: *) (b :: *). G a b => G (List a) (List b) where
  gop = undefined

instance forall (a :: *) (b :: *). F a b Bool => F (List a) (List b) Bool where
  fop = undefined

\x. x

