data Bool = True | False

data List (a :: *) = Cons a (List a) | Nil

data Nat = Succ Nat | Zero

data Maybe (a:: *) = Just a | Nothing

class Eq (a :: *) where
  eq :: a -> a -> Bool

instance Eq Bool where
  eq = \a. \b.
    case a of
       True -> case b of
                 True  -> True
                 False -> False
       False -> case b of
                  True  -> False
                  False -> True

id :: forall (a :: *). a -> a
   =  \x. x

main = id (eq True False)

main
