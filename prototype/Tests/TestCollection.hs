data List (a :: *) = Cons a (List a) | Nil

class forall (c :: *) (e :: *). Coll c e | c -> e where
  sing :: e -> c

instance forall (a :: *). Coll (List a) a where
  sing = \e. Cons e Nil

sing2 :: forall (e :: *). forall (c1 :: *). forall (c2 :: *). Coll c2 c1 => Coll c1 e => e -> c2
           = \x. sing (sing x)

sing2NoSig = \x. sing (sing x)

\x. x
