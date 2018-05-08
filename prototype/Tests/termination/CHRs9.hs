
data List (a :: *) = Nil | Cons a (List a)
data Bool = False | True
undefined = let x = x in x

class forall (a :: *) (b :: *) (c :: *). Mul a b c | a b -> c where
  mul :: a -> b -> c

instance forall (a :: *) (b :: *) (c :: *).
           Mul a b c => Mul a (List b) (List c) where
  mul = undefined

-- I THINK THAT THIS SHOULD FAIL TO TERMINATE
f = \b. \x. \y. case b of
                  False -> y
                  True  -> mul x (Cons y Nil)
-- BUT INSTEAD IT SEEMS TO FAIL (ERRONEOUSLY) WITH THE FOLLOWING:
--   Canonicity check failed on constraint : [F a b] ~ b
--
-- SINCE 'b' APPEARS IN A TYPE FAMILY APPLICATION, THIS SHOULD NOT TRIGGER AN
-- OCCURS CHECK (IF THAT IS WHY THE ERROR OCCURS).

\x. x

