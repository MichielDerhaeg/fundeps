
--  SHOULD SUCCEED (CASTING ENABLED)

class forall (a :: *) (b :: *). C a b | a -> b where
  c :: a -> a

data Nat  = Zero | Succ Nat


data Bool = True | False

instance C Nat Bool where
  c = \x. x

f :: forall (b :: *). C Nat b => b -> Bool
  =  \x. x

