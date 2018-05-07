
--  SHOULD FAIL (Violates FD)

data Bool = True | False
data Nat = Zero | Succ Nat
data Maybe (a :: *) = Nothing | Just a

class forall (a :: *) (b :: *). C a b | a -> b where
  cop :: a -> a

-- undefined :: forall a. a
undefined = let x = x in x

instance C Nat Bool where
  cop = undefined

instance forall (a :: *). C (Maybe a) a where
  cop = undefined

-- SHOULD COMPILE
--
-- Should create the following witness constraint schemes:
-- axiom g_uO () : FC0(Nat) ~ Bool
-- axiom g_uQ (t_uJ) : FC0(Maybe t_uJ) ~ t_uJ
\x. x

