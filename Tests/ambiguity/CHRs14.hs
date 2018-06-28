
class forall (p :: *) (q :: *). D p q where
  d :: p -> q

class forall (a :: *) (b :: *). C a b | a -> b where
  c :: a -> b

undefined = let x = x in x

data List (a :: *) = Nil | Cons a (List a)
data Char = MkChar       -- Placeholder
data Bool = True | False -- Placeholder

instance forall (a :: *) (b :: *). C a b => D (List a) b where
  d = undefined

instance D Char Bool where
  d = undefined

h :: forall (a :: *). forall (b :: *). D a b => a -> a
  =  undefined


-- SHOULD FAIL SINCE IT VIOLATES THE AMBIGUITY CONDITIONS.
-- NOTICE THAT THE CALL 'h (Cons MkChar (Cons MkChar Nil))'
-- IS NOT AMBIGUOUS BUT h's DEFINITION IS NONETHELESS

test1 :: forall (t :: *). C Char t => List Char
      = h (Cons MkChar (Cons MkChar Nil))
-- IN SUMMARY, IF WE DO NOT ENFORCE THE AMBIGUITY CONDITION
-- THIS DEFINITION SHOULD PASS, BUT CURRENTLY IT SEEMS TO FAIL

-- No signature
test2 = h (Cons MkChar (Cons MkChar Nil))

