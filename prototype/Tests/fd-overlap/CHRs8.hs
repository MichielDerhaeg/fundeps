
data Int   = MkInt   -- Placeholder
data Float = MkFloat -- Placeholder

undefined = let x = x in x

class forall (a :: *) (b :: *) (c :: *). Mul a b c | a b -> c where
  mul :: a -> b -> c

instance Mul Int Float Float where
  mul = undefined

instance Mul Int Float Int where
  mul = undefined

-- SHOULD FAIL: THE INSTANCES VIOLATE THE FUNCTIONAL DEPENDENCY
\x. x

