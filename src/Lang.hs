{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Lang where

import Data.List
import Debug.Trace

data Exp = ATOM Atom
         | PVA VName
         | PVE VName
         | CONS Exp Exp deriving Eq

instance Show Exp where
    show (ATOM "Nil") = "[]"
    show (ATOM name) = name
    show (PVA name) = "PVA " <> name
    show (PVE name) = "PVE " <> name
    show c@(CONS _ _) = "[" <> f c <> "]"
        where
          f (CONS x (ATOM "Nil")) = show x
          f (CONS x xs) = show x <> ", " <> f xs
          f (ATOM "Nil") = ""
          f x = show x

type Atom  = String
type AVar  = Exp
type EVar  = Exp
type Param = Exp
type AVal  = Exp
type EVal  = Exp
type AExp  = Exp
type Var   = Exp

type Prog = [FDef]

data FDef = DEFINE FName [Param] Term
    deriving (Eq, Show)

type FName = String
type VName = String

data Term = ALT Cond Term Term
          | CALL FName [Exp]
          | RETURN Exp
          deriving (Eq, Show)

data Cond = EQA' AExp AExp
          | CONS' Exp EVar EVar AVar
          deriving (Eq, Show)

data Bind = Var := Exp deriving Show
type Env = [Bind] 

type State = (Term, Env)

id_prog :: Prog
id_prog = [
  (DEFINE "Id" [e'x]
    (RETURN e'x))
  ] where e'x = (PVE "x")

---------

class APPLY a b where (/.) :: a -> b -> a

instance APPLY Exp Env where
 (ATOM a) /. env = ATOM a
 (CONS h t) /. env = CONS (h /. env) (t /. env)
 var /. env = head [ x | (v := x) <- env, v == var ]

instance APPLY a b => APPLY [a] b where
  xs /. y = map (/. y) xs

class UPDATE a where (+.) :: a -> a -> a

instance Eq Bind where
  (var1 := _) == (var2 := _) = (var1 == var2)

instance UPDATE Env where
  binds +. binds' = nub (binds' ++ binds)

mkEnv :: [Var] -> [EVal] -> Env
mkEnv = zipWith (\var val -> (var := val))

getDef :: FName -> Prog -> FDef
getDef fn p = head [ fd | fd@(DEFINE f _ _) <- p, f == fn ]

-----------

int :: Prog -> [EVal] -> EVal
int p d = eval s p
            where (DEFINE f prms _) : p' = p
                  e = mkEnv prms d
                  s = ((CALL f prms), e)

eval :: State -> Prog -> EVal
eval s@((CALL f args), e) p = trace ("call " <> f <> " " <> (show e')) $ eval s' p
                              where DEFINE _ prms t' = getDef f p
                                    e' = mkEnv prms (args /. e)
                                    s' = (t', e')

eval s@((ALT c t1 t2), e) p = case cond c e of
                               TRUE ue -> eval (t1, e +. ue) p
                               FALSE ue -> eval (t2, e +. ue) p

eval s@(RETURN exp, e) p = exp /. e

data CondRes = TRUE Env | FALSE Env

cond :: Cond -> Env -> CondRes
cond (EQA' x y)         e = let x' = x /. e; y' = y /. e in
                            case (x', y') of
                               (ATOM a, ATOM b) | a == b -> TRUE  []
                               (ATOM a, ATOM b)          -> FALSE []

cond (CONS' x vh vt va) e = let x' = x/.e in
                            case x' of
                                CONS h t -> TRUE  [vh := h, vt := t]
                                ATOM a   -> FALSE [va := x']

