
data List (a :: *) = Nil | Cons a (List a)
data Tup (a :: *) (b :: *) = MkTup a b

undefined = let x = x in x

zip2 :: forall (a :: *). forall (b :: *). List a -> List b -> List (Tup a b)
     = undefined

class forall (a :: *) (b :: *) (c :: *). Zip a b c | c -> b, c -> a where
  zip :: List a -> List b -> c

instance forall (a :: *) (b :: *). Zip a b (List (Tup a b)) where
  zip = zip2

instance forall (a :: *) (b :: *) (c :: *) (e :: *).
           Zip (Tup a b) c e => Zip a b (List c -> e) where -- THE PARSER CANNOT DEAL WITH ARROWS!
  zip = \as. \bs. \cs.
          zip (zip2 as bs) cs

