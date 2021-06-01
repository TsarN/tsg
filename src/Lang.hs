{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Lang where

import Data.List
import Data.Maybe
import Debug.Trace

import qualified Data.Text as T
import qualified Data.Map.Strict as M

data Exp = ATOM Atom
         | PVA VName
         | PVE VName
         | CVA Int
         | CVE Int
         | CONS Exp Exp deriving (Eq, Show, Ord)

reprList :: [Exp] -> Exp
reprList = foldr CONS (ATOM "Nil")

printExp (ATOM "Nil") = "[]"
printExp (ATOM name) = name
printExp (PVA name) = "PVA " <> name
printExp (PVE name) = "PVE " <> name
printExp (CVA name) = "CVA " <> T.pack (show name)
printExp (CVE name) = "CVE " <> T.pack (show name)
printExp c@(CONS _ _) = "[" <> f c <> "]"
    where
      f (CONS x (ATOM "Nil")) = printExp x
      f (CONS x xs) = printExp x <> ", " <> f xs
      f (ATOM "Nil") = ""
      f x = printExp x

type Atom  = T.Text
type AVar  = Exp
type EVar  = Exp
type Param = Exp
type AVal  = Exp
type EVal  = Exp
type AExp  = Exp
type Var   = Exp
type CVar  = Exp
type CVal  = Exp
type CExp  = Exp
type CEVar = Exp
type CEVal = Exp
type CEExp = Exp
type CAVar = Exp
type CAVal = Exp
type CAExp = Exp

type Prog = [FDef]

type FastProg = M.Map FName FDef

data FDef = DEFINE FName [Param] Term
    deriving (Eq, Show)

type FName = T.Text
type VName = T.Text

data Term = ALT Cond Term Term
          | CALL FName [Exp]
          | RETURN Exp
          | TRACE Exp Term
          deriving (Eq, Show)

data Cond = EQA' AExp AExp
          | CONS' Exp EVar EVar AVar
          deriving (Eq, Show)

type Env = M.Map Var Exp

type State = (Term, Env)

id_prog :: Prog
id_prog = [
  (DEFINE "Id" [e'x]
    (RETURN e'x))
  ] where e'x = (PVE "x")

---------

class APPLY a b where (/.) :: a -> b -> a

instance APPLY Exp Env where
    (ATOM a) /. s = ATOM a
    (CONS h t) /. s = CONS (h /. s) (t /. s)
    cvar /. s = fromMaybe cvar $ M.lookup cvar s

instance APPLY a b => APPLY [a] b where
  xs /. y = map (/. y) xs

class UPDATE a where (+.) :: a -> a -> a

instance UPDATE Env where
  a +. b = M.union b a

mkEnv :: [Var] -> [EVal] -> Env
mkEnv vars vals = M.fromList $ zip vars vals

getDef :: FName -> FastProg -> FDef
getDef fn p = case M.lookup fn p of
                Just x -> x
                Nothing -> error $ "no such function: " <> (T.unpack fn)

mkFastProg :: Prog -> FastProg
mkFastProg prog = M.fromList [ (name, def) | def@(DEFINE name _ _) <- prog]

-----------

int :: Prog -> [EVal] -> EVal
int p d = eval s (mkFastProg p)
            where (DEFINE f prms _) : p' = p
                  e = mkEnv prms d
                  s = ((CALL f prms), e)

eval :: State -> FastProg -> EVal
eval s@((CALL f args), e) p = eval s' p
                              where DEFINE _ prms t' = getDef f p
                                    e' = mkEnv prms (args /. e)
                                    s' = (t', e')

eval s@((ALT c t1 t2), e) p = case cond c e of
                               TRUE ue -> eval (t1, e +. ue) p
                               FALSE ue -> eval (t2, e +. ue) p

eval s@(RETURN exp, e) p = exp /. e
eval s@(TRACE exp t, e) p = trace (T.unpack $ "TRACE " <> (printExp (exp /. e))) $ eval (t, e) p

data CondRes = TRUE Env | FALSE Env

cond :: Cond -> Env -> CondRes
cond (EQA' x y)         e = let x' = x /. e; y' = y /. e in
                            case (x', y') of
                               (ATOM a, ATOM b) | a == b -> TRUE  M.empty
                               (ATOM a, ATOM b)          -> FALSE M.empty

cond (CONS' x vh vt va) e = let x' = x/.e in
                            case x' of
                                CONS h t -> TRUE  $ M.fromList [(vh, h), (vt, t)]
                                ATOM a   -> FALSE $ M.fromList [(va, x')]

