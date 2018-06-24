
data String = MkString -- Placeholder

class forall (a :: *). Show a where
  show :: a -> String

class forall (a :: *). Read a where
  read :: String -> a

f = \s. show (read s)

-- SHOULD FAIL DUE TO AMBIGUITY
-- UNFORTUNATELY NOW IT PASSES

