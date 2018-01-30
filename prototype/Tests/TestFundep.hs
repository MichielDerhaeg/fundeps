class () => Collection (c :: *) (e :: *) | c -> e where {
  singleton :: e -> c
}

class () => SomeClass (a :: *) (b :: *) (b :: *) | a -> b, a b -> c,c -> a b where {
  singleton :: e -> c
}

signleton
