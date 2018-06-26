
-- TEST SOME CONFLUENCE ISSUES

-- List definition in parts
data Nil = Nil
data Cons (a :: *) (b :: *) = Cons a b

data Tup (a :: *) (b :: *) = MkTup a b
data ExpAbs (x :: *) (a :: *) = ExpAbs x a

class forall (env :: *) (exp :: *) (t :: *). Eval env exp t | env exp -> t where
  eval :: env -> exp -> t

instance forall (x :: *) (v1 :: *) (env :: *) (exp :: *) (v2 :: *).
    Eval (Cons (Tup x v1) env) exp v2 => Eval env (ExpAbs x exp) (v1 -> v2) where
  eval = \env. \t. case t of
                     ExpAbs x exp -> \v. eval (Cons (MkTup x v) env) exp

-- NOT SURE ABOUT THIS EXAMPLE. THE ONLY THING I AM SURE OF IS THAT WE NEED TO
-- START PARSING ARROW TYPES.
