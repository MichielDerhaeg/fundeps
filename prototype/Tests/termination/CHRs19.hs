
class forall (a :: *) (b :: *) (c :: *). F a b c | a -> b where
  fop :: a -> b -> c

undefined = let x = x in x

data List (a :: *) = Nil | Cons a (List a)
data Char = MkChar       -- Placeholder
data Bool = True | False
data Nat  = Zero | Succ Nat

instance F Nat Bool Char where
  fop = undefined

instance forall (a :: *) (b :: *). F a b Bool => F (List a) (List b) Bool where
  fop = undefined

-- We need to check confluence; we need an example
-- of a function definition that triggers issues
