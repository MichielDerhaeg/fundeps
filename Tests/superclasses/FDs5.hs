
--  SHOULD SUCCEED (Extract the superclass from the dictionary)

data Bool = True | False

class forall (a :: *). Eq a where
  eq :: a -> a -> Bool

class forall (a :: *). Eq a => Ord a where
  ge :: a -> a -> Bool

not = \x. case x of
            True  -> False
            False -> True

and = \x. \y. case x of
                True  -> y
                False -> False

gt :: forall (a :: *). Ord a => a -> a -> Bool
   = \x. \y. and (ge x y) (not (eq x y))
