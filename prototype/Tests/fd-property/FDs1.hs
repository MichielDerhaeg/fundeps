
--  SHOULD FAIL (Violates FD)

class forall (c :: *) (e :: *). Coll c e | c -> e where
  sing :: e -> c

data Integer = MkInteger -- placeholder
data Bit     = MkBit     -- placeholder
data Byte    = MkByte    -- placeholder

instance Coll Integer Bit where
  sing = \x. MkInteger

instance Coll Integer Byte where
  sing = \x. MkInteger

\x. x

