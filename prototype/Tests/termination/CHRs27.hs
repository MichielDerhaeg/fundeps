
data List (a :: *) = Nil | Cons a (List a)
data Tup (a :: *) (b :: *) = MkTup a b
data Bool = True | False
data Char = MkChar -- Placeholder
data Nat  = Zero | Succ Nat
undefined = let x = x in x

zip2 :: forall (a :: *). forall (b :: *). List a -> List b -> List (Tup a b)
     = undefined

class forall (a :: *) (b :: *) (c :: *). Zip a b c | c -> b, c -> a where
  zip :: List a -> List b -> c

instance forall (a :: *) (b :: *). Zip a b (List (Tup a b)) where
  zip = zip2

-- || instance forall (a :: *) (b :: *) (c :: *) (e :: *).
-- ||            Zip (Tup a b) c e => Zip a b (List c -> e) where -- THE PARSER CANNOT DEAL WITH ARROWS!
-- ||   zip = \as. \bs. \cs.
-- ||           zip (zip2 as bs) cs

head = \xs. case xs of
              Nil       -> undefined
              Cons y ys -> y


e1 = head (zip (Cons True (Cons False Nil)) (Cons MkChar (Cons MkChar Nil)))

e2 = head (zip (Cons True (Cons False Nil))
               (Cons MkChar (Cons MkChar Nil))
               (Cons Zero (Cons Zero Nil))
          )

-- This fails while it shouldn't I think. Looks
-- like a bug or something I think.
\x. x

