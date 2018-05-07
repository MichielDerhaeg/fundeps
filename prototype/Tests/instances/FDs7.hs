
--  SHOULD FAIL (Violates FD)

data Bool = True | False

class forall (a :: *). Eq a where
  eq :: a -> a -> Bool

data List (a :: *) = Nil | Cons a (List a)

and = \x. \y. case x of
                True  -> y
                False -> False

instance forall (b :: *). Eq b => Eq (List b) where
  eq = \xss. \yss. case xss of
                     Nil       -> case yss of
                                    Nil       -> True
                                    Cons y ys -> False
                     Cons x xs -> case yss of
                                    Nil       -> False
                                    Cons y ys -> and (eq x y) (eq xs ys)

-- SHOULD COMPILE (and create d : forall b. TEq b -> TEq (List b))
\x. x

