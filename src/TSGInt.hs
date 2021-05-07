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
    repr (PVA name) = repr [ATOM "PVA", repr name]
    repr (PVE name) = repr [ATOM "PVE", repr name]

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
    repr (DEFINE name params term) = repr [ATOM "DEFINE", repr name, repr params, repr term]

instance Repr Term where
    repr (ALT cond true false) = repr [ATOM "ALT", repr cond, repr true, repr false]
    repr (CALL fname params) = repr [ATOM "CALL", repr fname, repr params]
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


util = [ Func "main"
       , Call "eq"
       , Return

       , Func "and"
       , If [ Return ]
       , Drop, Push "False", Return

       , Func "or"
       , If [ Drop, Push "True" ]
       , Return

       , Func "not"
       , If [ Push "False", Return ]
       , Push "True"
       , Return

       , Func "eqa"
       , Dup
       , Test
       , If [ Drop, Drop, Push "False", Return ]
       , Swap
       , Dup
       , Test
       , If [ Drop, Drop, Push "False", Return ]
       , Eqa
       , Return

       , Func "eqe"
       , Dup
       , Test
       , Call "not"
       , If [ Drop, Drop, Push "False", Return ]
       , Swap
       , Dup
       , Test
       , Call "not"
       , If [ Drop, Drop, Push "False", Return ]
       , Dup2
       , Split
       , Swap
       , Drop
       , Dup2
       , Split
       , Swap
       , Drop
       , Call "eq"
       , Call "not"
       , If [ Drop, Drop, Push "False", Return ]
       , Split
       , Drop
       , Swap
       , Split
       , Drop
       , Call "eq"
       , Return

       , Func "eq"
       , Dup2
       , Dup2
       , Call "eqa"
       , If [ Drop, Drop, Push "True", Return ]
       , Call "eqe"
       , Return
       ]

