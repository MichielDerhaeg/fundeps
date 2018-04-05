class forall (a :: *) (b :: *). C a b | a -> b where
  fc :: a -> b

data Nat = Suc Nat | Zero

data Bool = True | False

instance C Nat Bool where
  fc = \i. case i of
            Zero   -> False
            Suc i' -> True

f :: forall (b :: *). C Nat b => b -> Bool
   = \x. x

\x. x
