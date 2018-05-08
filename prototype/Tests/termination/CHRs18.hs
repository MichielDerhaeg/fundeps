

class forall (a :: *). Q a where
  q :: a

class forall (a :: *) (b :: *). R a b where
  r :: a -> b

data Bool  = MkBool  -- Placeholder
data Float = MkFloat -- Placeholder
data Char  = MkChar  -- Placeholder
data List (a :: *) = Nil | Cons a (List a)
undefined = let x = x in x

instance forall (a :: *) (b :: *). R a b => Q (List a) where
  q = undefined

instance R Bool Float where
  r = undefined

instance R Bool Char where
  r = undefined

exp1 :: List Bool
     = q
-- HA! I THOUGHT THAT WE ARE NOT CHECKING AMBIGUITY BUT I (CORRECTLY) GET THE
-- FOLLOWING ERROR:
--
-- || [HsTypeChecker failure]
-- || Ambigiuous context : bs : [b_uK],
-- ||                      as : [a_uJ],
-- ||                      class constraints : [R a_uJ b_uK]

-- TRICKY EXAMPLE. WE NEED TO LOOK AT THIS TOGETHER
\x. x

