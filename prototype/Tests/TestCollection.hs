data List (a :: *) = Cons a (List a) | Nil

class forall (c :: *) (e :: *). Collection c e | c -> e where
  singleton :: e -> c

instance forall (a :: *). Collection (List a) a where
  singleton = \e. Cons e Nil

singleton2 :: forall (e :: *). forall (c1 :: *). forall (c2 :: *). Collection c2 c1 => Collection c1 e => e -> c2
           = \x. singleton (singleton x)

singleton2NoSig = \x. singleton (singleton x)

\x. x
