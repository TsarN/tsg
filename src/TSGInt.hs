{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuasiQuotes #-}

module TSGInt where

import Lang
import SM
import Lisp

import Text.RawString.QQ (r)

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
--    repr (TRACE exp term) = repr [ATOM "TRACE", repr exp, repr term]

instance Repr Cond where
    repr (EQA' lhs rhs) = repr [ATOM "EQA'", repr lhs, repr rhs]
    repr (CONS' exp lhs rhs a) = repr [ATOM "CONS'", repr exp, repr lhs, repr rhs, repr a]

tsgInterpSourceCode :: String
tsgInterpSourceCode = [r|
(defun interpret (source args) (
    (uncons source source-head source-tail)
    (uncons source-head DEFINE source-head)
    (uncons source-head entry-point source-head)
    (set map (register-funcs Nil source))
    (cons RESULT (eval-term map Nil (cons CALL (cons entry-point (cons args Nil)))))
))

(defun eval-term (map env term) (
    (uncons term instr term-tail)

    (if (eq instr RETURN) (
        (uncons term-tail exp term-tail)
        (eval-exp env exp)
    ) (

    (if (eq instr ALT) (
        (uncons term-tail cond term-tail)
        (uncons term-tail alt-1 term-tail)
        (uncons term-tail alt-2 term-tail)
        (uncons (eval-cond env cond) env result)
        (if result
            (eval-term map env alt-1)
            (eval-term map env alt-2)
        )
    ) (

    (if (eq instr CALL) (
        (uncons term-tail func-name term-tail)
        (uncons term-tail func-args term-tail)
        (set func-args (eval-args env func-args))
        (set func-info (map-get map func-name))
        (uncons func-info func-params func-body)
        (set env (pass-params Nil func-args func-params))
        (eval-term map env func-body)
    )

    (panic))))))
))

(defun pass-params (env args params) (
    (if (uncons args args-head args-tail) (
        (uncons params params-head params-tail)
        (set env (map-set env params-head args-head))
        (pass-params env args-tail params-tail)
    ) env)
))

(defun eval-args (env args) (
    (if (uncons args args-head args-tail) (
        (cons (eval-exp env args-head) (eval-args env args-tail))
    ) Nil)
))

(defun eval-exp (env exp) (
    (if (uncons exp exp-head exp-tail) (
        (if (or (eq exp-head PVA) (eq exp-head PVE)) (
            (map-get env exp)
        ) (
            (cons (eval-exp env exp-head) (eval-exp env exp-tail))
        ))
    ) exp)
))

(defun eval-cond (env cond) (
    (uncons cond kind cond-tail)

    (if (eq kind EQA') (
        (uncons cond-tail lhs cond-tail)
        (uncons cond-tail rhs cond-tail)
        (set lhs (eval-exp env lhs))
        (set rhs (eval-exp env rhs))
        (cons env (eq lhs rhs))
    ) (
        (uncons cond-tail exp cond-tail)
        (uncons cond-tail e-var-1 cond-tail)
        (uncons cond-tail e-var-2 cond-tail)
        (uncons cond-tail a-var cond-tail)
        (set exp (eval-exp env exp))
        (if (uncons exp exp-head exp-tail) (
            (set env (map-set env e-var-1 exp-head))
            (set env (map-set env e-var-2 exp-tail))
            (cons env True)
        ) (
            (set env (map-set env a-var exp))
            (cons env False)
        ))
    ))
))

(defun register-funcs (map defines) (
    (if (uncons defines defines-head defines-tail) (
        (uncons defines-head DEFINE defines-head)
        (uncons defines-head func-name defines-head)
        (uncons defines-head func-args defines-head)
        (uncons defines-head func-body defines-head)
        (set map (map-set map func-name (cons func-args func-body)))
        (register-funcs map defines-tail)
    ) map)
))

(defun map-remove (map key) (
    (if (uncons map map-head map-tail) (
        (uncons map-head map-head-key map-head-value)
        (if (eq key map-head-key) map-tail 
            (cons map-head (map-remove map-tail key))
        )
    ) map)
))

(defun map-set (map key value) (
    (set map (map-remove map key))
    (cons (cons key value) map)
))

(defun map-get (map key) (
    (if (uncons map map-head map-tail) (
        (uncons map-head map-head-key map-head-value)
        (if (eq key map-head-key) map-head-value
            (map-get map-tail key)
        )
    ) Nil)
))

(defun not (x) (
    (if x False True)
))

(defun and (x y) (
    (if x y False)
))

(defun or (x y) (
    (if x True y)
))

(defun eq (x y) (
    (if (uncons x x-head x-tail) (
        (if (uncons y y-head y-tail) (
            (if (eq x-head y-head) (eq x-tail y-tail) False)
        ) False)
    ) (
        (if (uncons y y-head y-tail) False
         (eqa x y)
        )
    ))
))
|]

tsgInterp :: Prog
tsgInterp = compileSM $ compileLisp tsgInterpSourceCode

runTSGInterp :: Prog -> [Exp] -> Exp
runTSGInterp prog arg = int tsgInterp [repr $ reverse [repr prog, repr $ map repr arg]]
