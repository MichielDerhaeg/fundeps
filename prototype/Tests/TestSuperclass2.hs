data Bool = True | False

class () => D (a :: *) where {
  fd :: a -> a
}

class (D a) => A (a :: *) where {
  fa :: a -> a
}

class () => B (a :: *) where {
  fb :: a -> a
}

class (A a, B a) => C (a :: *) where {
  fc :: a -> a
}

class () => E (a :: *) where {
  fe :: a -> a
}

instance () => E Bool where {
  fe = \a. a
}

instance () => D Bool where {
  fd = \a. a
}

instance () => A Bool where {
  fa = \a. (fd a)
}

instance () => B Bool where {
  fb = \a. a
}

instance () => C Bool where {
  fc = \a. (fd (fb ( fa a )))
}

\a. fc (fb a)
