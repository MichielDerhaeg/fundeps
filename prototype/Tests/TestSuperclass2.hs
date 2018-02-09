data Bool = True | False

data List (a :: *) = Cons a (List a) | Nil

class forall (a :: *). D a where
  fd :: a -> a


class forall (a :: *). (D a) => A a where
  fa :: a -> a


class forall (a :: *). B a where
  fb :: a -> a


class forall (a ::*). (A a, B a) => C a where
  fc :: a -> a


class forall (a :: *). E a where
  fe :: a -> a


instance E Bool where
  fe = \a. a


instance D Bool where
  fd = \a. a


instance A Bool where
  fa = \a. (fd a)


instance B Bool where
  fb = \a. a


instance C Bool where
  fc = \a. (fd (fb ( fa a )))


instance forall (a :: *). (D a) => D (List a) where
  fd = \l. case l of
             Nil       -> Nil
             Cons x ls -> Cons (fd x) (fd ls)


instance forall (a :: *). (A a) => A (List a) where
  fa = \l. case l of
             Nil       -> Nil
             Cons x ls -> Cons (fa x) (fa ls)


\a. fc (fb a)
