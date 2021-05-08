{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TSGInt where

import Lang
import SM

-- Following data structures have representation at runtime:
--
-- Bool representation: (ATOM "True") | (ATOM "False")
-- List representation: (ATOM "Nil") | (CONS head tail)
-- Pair representation: (CONS fst snd)
-- Map representation: [(key, value)]
-- Char representation: Atom
-- String representation: [Char]
-- Function/variable name representation: String
-- Keyword representation: Atom
--
-- Input to the interpreter has the form as returned by repr :: Prog -> EVal

class Repr a where
    repr :: a -> EVal

instance Repr EVal where
    repr (ATOM a) = ATOM a
    repr (CONS head tail) = CONS (repr head) (repr tail)
    repr (PVA name) = repr [ATOM "PVA", ATOM name]
    repr (PVE name) = repr [ATOM "PVE", ATOM name]

instance Repr Char where
    repr c = ATOM [c]

instance Repr Bool where
    repr b = ATOM (show b)

instance Repr a => Repr [a] where
    repr [] = ATOM "Nil"
    repr (x:xs) = CONS (repr x) (repr xs)

instance (Repr a, Repr b) => Repr (a, b) where
    repr (x, y) = CONS (repr x) (repr y)

instance Repr FDef where
    repr (DEFINE name params term) = repr [ATOM "DEFINE", ATOM name, repr params, repr term]

instance Repr Term where
    repr (ALT cond true false) = repr [ATOM "ALT", repr cond, repr true, repr false]
    repr (CALL fname params) = repr [ATOM "CALL", ATOM fname, repr params]
    repr (RETURN exp) = repr [ATOM "RETURN", repr exp]

instance Repr Cond where
    repr (EQA' lhs rhs) = repr [ATOM "EQA'", repr lhs, repr rhs]
    repr (CONS' exp lhs rhs a) = repr [ATOM "CONS'", repr exp, repr lhs, repr rhs, repr a]


examples = [ ATOM "x"
           , ATOM "y"
           , ATOM "Nil"
           , repr [ATOM "x"]
           , repr [ATOM "y"]
           , repr [ATOM "y", ATOM "x"]
           , repr [ATOM "y", ATOM "Nil", ATOM "x"]
           , repr [ATOM "y", repr [ATOM "z"], ATOM "x"]
           ]

